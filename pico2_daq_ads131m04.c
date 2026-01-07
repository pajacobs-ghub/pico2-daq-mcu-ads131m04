// pico2_daq_ads131m04.c
//
// RP2350 Pico2 board as the DAQ-MCU, getting data from an ADS131M04 chip.
//
// PJ 2025-07-12: Adapt the interpreter from the BU79100G firmware.
//    2025-07-13: Functions to drive the ADS131M04 with default settings.
// JM 2025-11-09: Added OSR writing.
// JM 2025-11-10: Ported PJ's changes to fix EVENT# GPIO pull-ups.
// PJ 2026-01-07: Service the Real-Time Data Port (RTDP) with the second core.
//                Essentially a copy of the corresponding code developed for
//                the Pico2+BU79100G DAQ board.

#include "pico/stdlib.h"
#include "pico/multicore.h"
#include "pico/util/queue.h"
#include "hardware/clocks.h"
#include "hardware/gpio.h"
#include "hardware/uart.h"
#include "hardware/timer.h"
#include "hardware/spi.h"
#include "hardware/dma.h"
#include "hardware/pwm.h"
#include "pico/binary_info.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <ctype.h>

#define VERSION_STR "v0.44 Pico2 as DAQ-MCU 2026-01-08"

// Names for the GPIO pins.
// A. For interaction with the PIC18F26Q71 COMMS-MCU.
// UART0_TX on GP0 (default)
// UART0_RX in GP1 (default)
const uint READY_PIN = 22;
const uint FLAG_PIN = 26;
const uint Pico2_EVENT_PIN = 3;
const uint SYSTEM_EVENTn_PIN = 2;
// B. For interaction with the ADS131M04 ADC chip.
const uint SYNCHn_PIN = 7;
const uint CLKIN_PIN = 8;
const uint SPI1_CSn_PIN = 9;
const uint SPI1_CLK_PIN =10 ;
const uint SPI1_TX_PIN = 11;
const uint SPI1_RX_PIN = 12;
const uint DRDYn_PIN = 13;
// C. For implementing the Real-Time Data Port.
const uint SPI0_CSn_PIN = 17;
const uint SPI0_SCK_PIN = 18;
const uint SPI0_TX_PIN = 19;
const uint RTDP_DE_PIN = 20;
const uint RTDP_REn_PIN = 21;
const uint DATA_RDY_PIN = 27;


static inline void assert_ready()
{
    gpio_put(READY_PIN, 1);
}

static inline void assert_not_ready()
{
    gpio_put(READY_PIN, 0);
}

static inline void assert_event()
{
	gpio_put(Pico2_EVENT_PIN, 1);
}

static inline void release_event()
{
	gpio_put(Pico2_EVENT_PIN, 0);
}

static inline void raise_flag_pin()
{
	gpio_put(FLAG_PIN, 1);
}

static inline void lower_flag_pin()
{
	gpio_put(FLAG_PIN, 0);
}

static inline uint8_t read_system_event_pin()
{
	return (uint8_t) gpio_get(SYSTEM_EVENTn_PIN);
}

const uint LED_PIN = PICO_DEFAULT_LED_PIN;
uint8_t override_led = 0;

static inline void sampling_LED_ON()
{
    gpio_put(LED_PIN, 1);
}

static inline void sampling_LED_OFF()
{
    gpio_put(LED_PIN, 0);
}

static inline void assert_data_ready()
{
    gpio_put(DATA_RDY_PIN, 1);
}

static inline void clear_data_ready()
{
    gpio_put(DATA_RDY_PIN, 0);
}

static inline void enable_RTDP_transceiver()
{
    gpio_put(RTDP_REn_PIN, 0);
    gpio_put(RTDP_DE_PIN, 1);
}

static inline void disable_RTDP_transceiver()
{
    gpio_put(RTDP_REn_PIN, 1);
    gpio_put(RTDP_DE_PIN, 0);
}

// Unlike the AVR DAQ firmware, we are going to hard-code the number of
// channels at 4 (because we are using a single ADS131M04 chip) and we
// are going to use int32_t as the sample type.

// A place for the current sample set.
#define N_CHAN 4
static int32_t sample_data[N_CHAN];

// A place to collect the sample sets as they come in from the ADC chips.
#define N_FULLWORDS 0x00010000
#define MAX_N_SAMPLES (N_FULLWORDS/4)
int32_t data[N_FULLWORDS];
uint32_t next_fullword_index_in_data;
uint8_t fullword_index_has_wrapped_around;
uint32_t trigger_fullword_index; // Index in data[] where trigger occurred

// We are going to communicate with the ADS131M04 with its default word size
// of 24 bits and a full frames of 6 words but we will look at this data as
// 18 bytes when interacting with the Pico2's SPI module.
# define N_BYTES_IN_FRAME 18
static uint8_t incoming_bytes_adc[N_BYTES_IN_FRAME];
static uint8_t outgoing_bytes_adc[N_BYTES_IN_FRAME];

static int sampling_error_flag;

// Parameters controlling the device are stored in virtual config registers.
#define NUMREG 8
int32_t vregister[NUMREG];

void set_registers_to_original_values()
{
	// Reduced frequency to convert accurately on strip-board and Jeremy's PCB REV.1
    vregister[0] = 8192/4; // Master clock frequency f_CLKIN for ADS131M04, in kHz
    vregister[1] = 1024;   // Over-sampling ratio for the ADS131M04, default 1024.
    vregister[2] = 128;    // number of samples in record after trigger event
    vregister[3] = 0;      // trigger mode 0=immediate, 1=internal, 2=external
    vregister[4] = 0;      // trigger channel for internal trigger
    vregister[5] = 10000;  // trigger level as a signed integer
    vregister[6] = 1;      // trigger slope 0=sample-below-level 1=sample-above-level
    vregister[7] = 0;      // advertising period (in microseconds) for the RTDP
}
//
// core1 services the Real-Time Data Port
// which makes a snapshot of the sampled data available
// to an external SPI master device.
//
// The main loop of the RTDP service function acts upon commands
// sent from core0 via the queue.
//
queue_t RTDP_command_fifo;
#define RTDP_FIFO_LENGTH 1
// The commands themselves are uint values.
#define RTDP_NOP 0
#define RTDP_STOP 99
#define RTDP_ADVERTISE_NEW_DATA 1
// [FIX-ME] Maybe we should use an atomic variable to indicate the status.
static uint RTDP_status;
// The status values are also uint values.
#define RTDP_IDLE 0
#define RTDP_BUSY 1
// core0 will drop a copy of new sample data here.
static int32_t RTDP_data_words[N_CHAN];

void __no_inline_not_in_flash_func(core1_service_RTDP)(void)
{
    uint8_t tx_buffer[N_CHAN*4]; // Send out the data from this buffer.
    // The data sheet seems to indicate that we have to collect
    // the incoming data, even if we don't want it.
    uint8_t rx_buffer[N_CHAN*4]; // Dump the unwanted data here.
    //
    // Transfer bytes to and from the SPI peripheral via DMA channels.
    const uint dma_spi0_tx = dma_claim_unused_channel(true);
    const uint dma_spi0_rx = dma_claim_unused_channel(true);
    dma_channel_config tx_cfg = dma_channel_get_default_config(dma_spi0_tx);
    dma_channel_config rx_cfg = dma_channel_get_default_config(dma_spi0_rx);
    channel_config_set_transfer_data_size(&tx_cfg, DMA_SIZE_8);
    channel_config_set_read_increment(&tx_cfg, true);
    channel_config_set_write_increment(&tx_cfg, false);
    channel_config_set_transfer_data_size(&rx_cfg, DMA_SIZE_8);
    channel_config_set_read_increment(&rx_cfg, false);
    channel_config_set_write_increment(&rx_cfg, true);
    //
    uint timeout_period_us = vregister[7];
    // At 2MHz, 16 bytes transfer in about 64us,
    // so it does not make much sense to have a very short timeout.
    if (timeout_period_us < 100) timeout_period_us = 100;
    //
    // The main responsibility of core1 is to look for incoming commands and act.
    // This provides a synchronization mechanism, such that core1 advertises
    // available data only when core0 has put some new data into RTP_data_words,
    // and core0 will only put new data in that array while core1 is active and idle.
    //
    RTDP_status = RTDP_IDLE;
    bool my_spi_is_initialized = false;
    bool active = true;
    while (active) {
        // Wait until we are commanded to do something.
        uint cmd = RTDP_NOP;
        queue_remove_blocking(&RTDP_command_fifo, &cmd);
        switch (cmd) {
        case RTDP_ADVERTISE_NEW_DATA:
            { // start new scope
                RTDP_status = RTDP_BUSY;
                for (uint i=0; i < N_CHAN; i++) {
                    // Put the data into the outgoing byte buffer in big-endian layout.
                    tx_buffer[4*i] = (uint8_t) (RTDP_data_words[i] >> 24);
                    tx_buffer[4*i+1] = (uint8_t) (RTDP_data_words[i] >> 16);
                    tx_buffer[4*i+2] = (uint8_t) (RTDP_data_words[i] >> 8);
                    tx_buffer[4*i+3] = (uint8_t) RTDP_data_words[i];
                }
                if (!my_spi_is_initialized) {
                    // We (conditionally) do the SPI module initialization here
                    // because it may have been deinitialized by a timeout event,
                    // or this may be the first use.
                    // My reading of Section 12.3.4.4. Clock ratios in the data sheet
                    // seems to indicate that we are limited to about 2MHz serial clock
                    // in slave mode.
                    // If we don't care about the MOSI data, we might go faster.
                    spi_init(spi0, 2000*1000);
                    spi_set_slave(spi0, true);
                    spi_set_format(spi0, 8, SPI_CPOL_1, SPI_CPHA_1, SPI_MSB_FIRST);
                    gpio_set_function(SPI0_CSn_PIN, GPIO_FUNC_SPI);
                    gpio_pull_up(SPI0_CSn_PIN);
                    gpio_set_function(SPI0_SCK_PIN, GPIO_FUNC_SPI);
                    gpio_pull_up(SPI0_SCK_PIN);
                    gpio_set_function(SPI0_TX_PIN, GPIO_FUNC_SPI);
                    // The dma-transfer requests are paced by the SPI peripheral.
                    channel_config_set_dreq(&tx_cfg, spi_get_dreq(spi0, true)); // tx
                    channel_config_set_dreq(&rx_cfg, spi_get_dreq(spi0, false)); // rx
                    my_spi_is_initialized = true;
                }
                dma_channel_configure(dma_spi0_tx, &tx_cfg,
                                      &spi_get_hw(spi0)->dr, // write address
                                      tx_buffer, // read address
                                      dma_encode_transfer_count(N_CHAN*2),
                                      false); // start later...
                dma_channel_configure(dma_spi0_rx, &rx_cfg,
                                      rx_buffer, // write address
                                      &spi_get_hw(spi0)->dr, // read address
                                      dma_encode_transfer_count(N_CHAN*2),
                                      false); // start later...
                // At this point, the data bytes are ready to be sent via SPI0,
                // so we can signal to the external supervisor device that there
                // is data to collect.
                dma_start_channel_mask((1u << dma_spi0_tx) | (1u << dma_spi0_rx));
                assert_data_ready();
                // It is up to the external device to collect all of the data
                // by selecting the Pico2 as a slave SPI device and clocking out
                // all of the bytes.
                uint64_t timeout = time_us_64() + timeout_period_us;
                // Wait for selection by the SPI-master device.
                // If this does not happen within a reasonable time,
                // we presume that the SPI-master device is not present
                // or not paying attention to the DATA_RDY signal,
                // so we cancel the data transfer.
                while (gpio_get(SPI0_CSn_PIN)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                enable_RTDP_transceiver();
                // Wait for the data to be clocked out.
                while (dma_channel_is_busy(dma_spi0_tx) ||
                       dma_channel_is_busy(dma_spi0_rx)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                // Wait for deselection by the SPI-master device.
                while (!gpio_get(SPI0_CSn_PIN)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                // If we arrive here then the data has been transferred through
                // the SPI peripheral
                goto finish;
            timed_out:
                spi_deinit(spi0);
                dma_channel_cleanup(dma_spi0_tx);
                dma_channel_cleanup(dma_spi0_rx);
                my_spi_is_initialized = false;
            finish:
                disable_RTDP_transceiver();
                clear_data_ready();
                RTDP_status = RTDP_IDLE;
            } // end new scope
            break;
        case RTDP_STOP:
            spi_deinit(spi0);
            dma_channel_cleanup(dma_spi0_tx);
            dma_channel_cleanup(dma_spi0_rx);
            my_spi_is_initialized = false;
            clear_data_ready();
            RTDP_status = RTDP_IDLE;
            active = false;
            break;
        default:
            {} // do nothing for any other command value
        }
    } // end while
    dma_channel_unclaim(dma_spi0_tx);
    dma_channel_unclaim(dma_spi0_rx);
} // end void core1_service_RTDP()

//
// core0 services the main sampling activity.
//

static inline uint32_t oldest_fullword_index_in_data()
{
    return (fullword_index_has_wrapped_around) ? next_fullword_index_in_data : 0;
}

void clear_data_array()
{
    // Clear the data[N_FULLWORDS] array to all zeros.
    for (uint32_t i = 0; i < N_FULLWORDS; ++i) {
        data[i] = 0;
    }
}

static inline int assert_adc_synch(uint32_t duration_us, uint64_t timeout)
{
    // We assume that the master clock to the ADS131M04 is already running.
    // To meet the timing requirement in Figure 6-2 of the ADS131M04 data sheet,
    // wait for a trailing edge of CLKIN and then pulse the SYNCH pin low.
    // This waiting will timeout if CLKIN is not running.
    while (!gpio_get(CLKIN_PIN)) {
        if (time_reached(timeout)) return 1;
    }
    while (gpio_get(CLKIN_PIN)) {
        if (time_reached(timeout)) return 1;
    }
    gpio_put(SYNCHn_PIN, 0);
    busy_wait_us(duration_us);
    gpio_put(SYNCHn_PIN, 1);
    return 0;
}

static inline int wait_for_adc_data_ready(uint64_t timeout)
{
    while (gpio_get(DRDYn_PIN)) {
        if (time_reached(timeout)) return 1;
    }
    return 0;
}

static inline void set_adc_command(uint16_t cmd)
{
    outgoing_bytes_adc[0] = (uint8_t)((cmd & 0xff00) >> 8);
    outgoing_bytes_adc[1] = (uint8_t)(cmd & 0x00ff);
    for (uint i = 2; i < N_BYTES_IN_FRAME; ++i) {
        outgoing_bytes_adc[i] = (uint8_t)0;
    }
}

static inline void write_adc_register(uint8_t reg_addr, uint16_t reg_value)
// Write a 16-bit value to an ADS131M04 register.
// The WREG command format is: 010a aaaa annn nnnn
// where a is the register address and n is the number of registers to write minus 1.
// For a single register write, n=0.
{
    uint16_t cmd = 0x4000 | ((reg_addr & 0x1F) << 7); // WREG command with address
    outgoing_bytes_adc[0] = (uint8_t)((cmd & 0xff00) >> 8);
    outgoing_bytes_adc[1] = (uint8_t)(cmd & 0x00ff);
    outgoing_bytes_adc[2] = (uint8_t)((reg_value & 0xff00) >> 8);
    outgoing_bytes_adc[3] = (uint8_t)(reg_value & 0x00ff);
    for (uint i = 4; i < N_BYTES_IN_FRAME; ++i) {
        outgoing_bytes_adc[i] = (uint8_t)0;
    }
}

static inline void set_adc_osr(uint32_t OSR)
// Set the oversampling ratio by writing to the CLOCK register (0x01).
// This function preserves channel enable bits (all enabled) and sets appropriate power mode.
// OSR values: 64(TBM), 128, 256, 512, 1024, 2048, 4096, 8192, 16256
{
    uint16_t clock_reg = 0x0F00; // All channels enabled (bits 11:8)
    //
    // Set OSR bits based on value
    if (OSR == 64) {
        clock_reg |= 0x0020; // Set TBM bit (bit 5), OSR[2:0] should be 000
        // Don't set OSR[2:0] bits, they stay at 0
    } else {
        // Clear TBM bit (bit 5) and set OSR[2:0] in bits 4:2
        uint8_t osr_bits;
        switch (OSR) {
            case 128:   osr_bits = 0; break;
            case 256:   osr_bits = 1; break;
            case 512:   osr_bits = 2; break;
            case 1024:  osr_bits = 3; break; // default
            case 2048:   osr_bits = 4; break;
            case 4096:  osr_bits = 5; break;
            case 8192:  osr_bits = 6; break;
            case 16256: osr_bits = 7; break;
            default:    osr_bits = 3; break; // default to 1024 if invalid
        }
        clock_reg |= (osr_bits << 2);
    }
    //
    // Set power mode to High-resolution (bits 1:0 = 10b)
    clock_reg |= 0x0002;
    //
    write_adc_register(0x01, clock_reg);
}

static inline void read_full_adc_frame()
{
    gpio_put(SPI1_CSn_PIN, 0); // Select the ADS131M04.
    busy_wait_us(1);
    spi_write_read_blocking(spi1, outgoing_bytes_adc, incoming_bytes_adc, N_BYTES_IN_FRAME);
    gpio_put(SPI1_CSn_PIN, 1); // Deselect.
}

static inline void unpack_adc_sample_data()
{
    for (int ch=0; ch < N_CHAN; ++ch) {
        int32_t word = 0L;
        uint ib = (1+ch)*3; // index of the high-byte for channel ch.
        word |= (uint32_t)incoming_bytes_adc[ib] << 16;
        word |= (uint32_t)incoming_bytes_adc[ib+1] << 8;
        word |= (uint32_t)incoming_bytes_adc[ib+2];
        // Sign-extend to the full 32-bit word.
        if (word & (1L << 23)) word |= 0xFF000000L;
        sample_data[ch] = word;
    }
}

int __no_inline_not_in_flash_func(sample_channels)(void)
// Sample the analog channels periodically and store the data in SRAM.
//
// For mode=0, we will consider that the trigger event is immediate, at sample 0,
// and the record will stop after a specified number of samples.
// So long as the record does not wrap around, the oldest sample set will start at
// byte address 0.
//
// For mode=1 or 2, we will start sampling into the SRAM circular buffer
// for an indefinite number of samples, while waiting for the trigger event.
// Once the trigger event happens, we will continue the record for a specified
// number of samples.  Because we do not keep a record of the number of times
// that the SRAM address wraps around, we just assume that the oldest sample
// starts at the next word address to be used to store a sample.
//
// Returns 0 on success, non-zero if the ADS131M04 does not have data ready when expected.
//
{
    // Get configuration data from virtual registers.
    uint32_t f_CLKIN_kHz = vregister[0];
    uint32_t OSR = vregister[1];
    int32_t sample_period_us = 2000L * OSR / f_CLKIN_kHz;
    //
    uint8_t mode = (uint8_t)vregister[3];
# define TRIGGER_IMMEDIATE 0
# define TRIGGER_INTERNAL 1
# define TRIGGER_EXTERNAL 2
    uint8_t trigger_chan = (uint8_t)vregister[4];
    uint16_t trigger_level = (uint16_t) vregister[5];
    uint8_t trigger_slope = (uint8_t)vregister[6];
    //
    bool service_RTDP = (vregister[7] != 0);
    uint cmd = RTDP_STOP;
    if (service_RTDP) {
        queue_init(&RTDP_command_fifo, sizeof(uint), RTDP_FIFO_LENGTH);
        multicore_launch_core1(core1_service_RTDP);
    }
    //
    sampling_error_flag = 0;
    next_fullword_index_in_data = 0; // Start afresh, at index 0.
    fullword_index_has_wrapped_around = 0;
    trigger_fullword_index = 0; // Will be updated when trigger occurs
    uint8_t post_event = 0;
    uint32_t samples_remaining = vregister[2];
    //
    // Start driving the ADS131M04 with a master clock via a PWM slice.
    // According to table in the RP2350 data sheet,
    // we use PWM slice 4A on GPIO8 (CLKIN_PIN).
    uint slice_num = pwm_gpio_to_slice_num(CLKIN_PIN);
    pwm_set_wrap(slice_num, 3);
    pwm_set_enabled(slice_num, false); // In case it has been left on from previous sampling.
    pwm_set_chan_level(slice_num, PWM_CHAN_A, 2);
    uint f_clk_sys = frequency_count_khz(CLOCKS_FC0_SRC_VALUE_CLK_SYS);
    float div = (float)f_clk_sys / f_CLKIN_kHz / 4;
    pwm_set_clkdiv(slice_num, div);
    pwm_set_enabled(slice_num, true);
    busy_wait_us(500); // Let the ADS131M04 clock and internal circuits settle.
    //
    set_adc_command(0); // NULL command; we just want to read sampled data.
    //
    // Set the OSR in the CLOCK register before the first SYNC.
    set_adc_osr(OSR);
    // After writing a register, wait for response with a generous timeout.
    uint64_t timeout = time_us_64() + 10000; // 10ms timeout
    if (wait_for_adc_data_ready(timeout)) return 4;
    busy_wait_us(1);
    read_full_adc_frame(); // Read response frame from register write.
    //
    // Assert the SYNCHn pin to reset the ADS131M04 and activate the new OSR setting.
    timeout = time_us_64() + 10;
    uint64_t period_CLKIN_ns = 1000000 / f_CLKIN_kHz;
    if (assert_adc_synch(3*period_CLKIN_ns, timeout)) return 99;
    //
    // After SYNC, the filter needs time to settle based on the OSR value.
    // Per datasheet Table 7-15, settling times vary by OSR (in CLKIN cycles):
    // OSR=64:728, 128:856, 256:1112, 512:1624, 1024:2648, 2048:4696, 4096:8792, 8192:16984, 16384:33368
    uint32_t settling_time_clkin_cycles;
    switch (OSR) {
        case 64:    settling_time_clkin_cycles = 728; break;
        case 128:   settling_time_clkin_cycles = 856; break;
        case 256:   settling_time_clkin_cycles = 1112; break;
        case 512:   settling_time_clkin_cycles = 1624; break;
        case 1024:  settling_time_clkin_cycles = 2648; break;
        case 2048:  settling_time_clkin_cycles = 4696; break;
        case 4096:  settling_time_clkin_cycles = 8792; break;
        case 8192:  settling_time_clkin_cycles = 16984; break;
        case 16256: settling_time_clkin_cycles = 33368; break;
        default:    settling_time_clkin_cycles = 2648; break; // default for OSR=1024
    }
    // Convert settling time from CLKIN cycles to microseconds
    // settling_time_us = settling_time_clkin_cycles / f_CLKIN_kHz * 1000
    uint32_t settling_time_us = (settling_time_clkin_cycles * 1000) / f_CLKIN_kHz;
    //
    // Wait for the settling time, then discard settled data frames.
    // We need to read at least 3 frames to clear the pipeline.
    busy_wait_us(settling_time_us);
    for (int i = 0; i < 3; i++) {
        timeout = time_us_64() + sample_period_us + 1000;
        if (wait_for_adc_data_ready(timeout)) return (1 + i);
        busy_wait_us(1);
        read_full_adc_frame();
    }
    //
    while (samples_remaining > 0) {
        sampling_LED_ON();
        raise_flag_pin(); // to allow timing via a logic probe.
        //
        // Take the analog sample set.
        // Keep timeout tight to avoid FIFO issues (max 2 samples in FIFO)
        timeout = time_us_64() + sample_period_us + 1000;
        if (wait_for_adc_data_ready(timeout)) return 3;
        busy_wait_us(1);
        read_full_adc_frame();
        unpack_adc_sample_data();
        for (uint ch=0; ch < N_CHAN; ++ch) {
            data[next_fullword_index_in_data+ch] = sample_data[ch];
        }
        //
        if (service_RTDP
            && (queue_is_empty(&RTDP_command_fifo))
            && RTDP_status == RTDP_IDLE) {
            for (uint ch=0; ch < N_CHAN; ++ch) {
                RTDP_data_words[ch] = sample_data[ch];
            }
            cmd = RTDP_ADVERTISE_NEW_DATA;
            queue_add_blocking(&RTDP_command_fifo, &cmd);
        }
        //
        if (post_event) {
            // Trigger event has happened.
            samples_remaining--;
        } else {
            // We need to decide about trigger event.
            switch (mode) {
            case TRIGGER_IMMEDIATE:
                post_event = 1;
                trigger_fullword_index = next_fullword_index_in_data;
                assert_event();
                break;
            case TRIGGER_INTERNAL: {
                // Pick the particular channel value out of the recently-stored data.
                int32_t s = sample_data[trigger_chan];
                if ((trigger_slope == 1 && s >= trigger_level) ||
                    (trigger_slope == 0 && s <= trigger_level)) {
                    post_event = 1;
                    trigger_fullword_index = next_fullword_index_in_data;
                    assert_event();
                }
                }
                break;
            case TRIGGER_EXTERNAL:
                if (read_system_event_pin() == 0) {
                    post_event = 1;
                    trigger_fullword_index = next_fullword_index_in_data;
                }
            } // end switch
        }
        // Point to the next available fullword index.
        next_fullword_index_in_data += 4;
        if (next_fullword_index_in_data >= N_FULLWORDS) {
            next_fullword_index_in_data -= N_FULLWORDS;
            fullword_index_has_wrapped_around = 1;
        }
        lower_flag_pin();
        sampling_LED_OFF();
    } // end while (main sampling loop)
    //
    if (service_RTDP) {
        while (queue_is_full(&RTDP_command_fifo)) {
            tight_loop_contents();
        }
        cmd = RTDP_STOP;
        queue_add_blocking(&RTDP_command_fifo, &cmd);
        while ((queue_is_full(&RTDP_command_fifo))
               || (RTDP_status == RTDP_BUSY)) {
            // We wait for the last RTDP command to finish.
            tight_loop_contents();
        }
        queue_free(&RTDP_command_fifo);
        multicore_reset_core1();
    }
    //
    pwm_set_enabled(slice_num, false);
    // If we arrive here, there have been no observed failures.
    return 0;
} // end int sample_channels()

void sample_channels_once()
{
    // We temporarily override some of the registers to make this happen.
    uint8_t mode_save = (uint8_t)vregister[3];
    uint16_t samples_remaining_save = (uint16_t)vregister[2];
    //
    vregister[3] = 0; // Immediate mode.
    vregister[2] = 1; // One sample set.
    // Note that, even though we ask for one sample,
    // two sample reads will be made because there will be 1 sample
    // leading to the immediate trigger event and one after trigger.
    // It should not matter.
    sampling_error_flag = sample_channels();
    //
    // Restore register values.
    vregister[3] = mode_save;
    vregister[2] = samples_remaining_save;
    return;
} // end sample_channels_once()

#define NSTRBUF1 128
char str_buf1[NSTRBUF1];
#define NSTRBUF2 16
char str_buf2[NSTRBUF2];

char* sample_set_to_str(uint32_t n)
{
    // Start with index of oldest sample, then move to selected sample.
    uint32_t word_index = oldest_fullword_index_in_data() + 4*n;
    // Assume that the fullword sets in the data wrap neatly.
	if (word_index > N_FULLWORDS) { word_index -= N_FULLWORDS; }
    snprintf(str_buf1, NSTRBUF1, "%d", data[word_index+0]);
    for (uint8_t ch=1; ch < N_CHAN; ch++) {
        snprintf(str_buf2, NSTRBUF2, " %d", data[word_index+ch]);
        strncat(str_buf1, str_buf2, NSTRBUF2);
    }
    return str_buf1;
}


// For incoming serial comms
#define NBUFA 80
char bufA[NBUFA];

int getstr(char* buf, int nbuf)
// Read (without echo) a line of characters into the buffer,
// stopping when we see a new-line character.
// Returns the number of characters collected,
// excluding the terminating null character.
{
	memset(buf, '\0', nbuf);
    int i = 0;
    char c;
    uint8_t done = 0;
    while (!done) {
        c = getc(stdin);
        if (c != '\n' && c != '\r' && c != '\b' && i < (nbuf-1)) {
            // Append a normal character.
            buf[i] = c;
            i++;
        }
        if (c == '\n') {
            done = 1;
            buf[i] = '\0';
        }
        if (c == '\b' && i > 0) {
            // Backspace.
            i--;
        }
    }
    return i;
} // end getstr()

int trim_string(char *str)
// Trim space characters from the start and end of the string.
// We assume that the string is properly null terminated.
// Returns the number of characters in the trimmed string, excluding the terminating '\0'.
{
	int len = strlen(str);
	if (len == 0) return 0;
	int start = 0;
	while (isspace((unsigned char)str[start])) {
		start += 1;
	}
	if (start == len) {
	    // There are no non-space characters left.
		str[0] = '\0';
		return 0;
	}
	// At this point, we have at least one non-space character.
	if (start > 0) {
		// Move all remaining characters.
		memmove(str, str+start, len-start);
		len -= start;
	}
	str[len] = '\0';
	int last = len - 1;
	while ((last >= 0) && isspace((unsigned char)str[last])) {
		str[last] = '\0';
		last -= 1;
	}
	return last+1; // final string length
}

void interpret_command(char* cmdStr)
// The first character in the string specifies the command.
// Any following text is interpreted as delimiter-separated integers
// and used as arguments for the command.
// A successful command should echo the first character,
// followed by any results as the message.
// A command that does not do what is expected should return a message
// that includes the word "error".
{
    char* token_ptr;
    const char* sep_tok = ", ";
    uint8_t i;
	int16_t v;
    // printf("DEBUG: DAQ MCU cmdStr=\"%s\"", cmdStr);
    if (!override_led) gpio_put(LED_PIN, 1); // To indicate start of interpreter activity.
    switch (cmdStr[0]) {
	case 'v':
		// Report version string and (some) configuration details.
		uint f_clk_sys = frequency_count_khz(CLOCKS_FC0_SRC_VALUE_CLK_SYS);
		printf("v %s ADS131M04 %d kHz\n", VERSION_STR, f_clk_sys);
		break;
	case 'L':
		// Turn LED on or off.
		// Turning the LED on by command overrides its use
		// as an indicator of interpreter activity.
		token_ptr = strtok(&cmdStr[1], sep_tok);
		if (token_ptr) {
			// Found some non-blank text; assume on/off value.
			// Use just the least-significant bit.
			i = (uint8_t) (atoi(token_ptr) & 1);
			gpio_put(LED_PIN, i);
			override_led = i;
			printf("L %d\n", i);
		} else {
			// There was no text to give a value.
			printf("L error: no value\n");
		}
		break;
	case 'n':
		// Report number of virtual registers.
		printf("n %d\n", NUMREG);
		break;
    case 'r':
        // Report a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                v = vregister[i];
                printf("r %d\n", v);
            } else {
                printf("r error: invalid register.\n");
            }
        } else {
            printf("r error: no register specified.\n");
        }
        break;
    case 's':
        // Set a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text; assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                token_ptr = strtok(NULL, sep_tok);
                if (token_ptr) {
                    // Assume text is value for register.
                    v = (int) atoi(token_ptr);
                    // Accept user-specified value.
                    vregister[i] = v;
                    printf("s reg[%u] set to %d\n", i, v);
                } else {
                    printf("s error: no value given.\n");
                }
            } else {
                printf("s error: invalid register.\n");
            }
        } else {
            printf("s error: no register specified.\n");
        }
        break;
    case 'F':
        // Set the values of the registers to those values hard-coded
        // into this firmware.  A factory default, so to speak.
        set_registers_to_original_values();
        printf("F registers reset\n");
        break;
    case 'g':
        // Start the sampling process.
        // What happens next, and when it happens, depends on the
        // register settings and external signals.
        printf("g start sampling\n");
        // The task takes an indefinite time,
        // so let the COMMS_MCU know via busy# pin.
        assert_not_ready();
        sampling_error_flag = sample_channels();
        assert_ready();
        break;
    case 'k':
        // Report the value of the sampling_error_flag flag.
        printf("k %u\n", sampling_error_flag);
        break;
    case 'I':
        // Immediately take a single sample set and report values.
        sample_channels_once();
        // Send back the second set of samples to allow
        // the ADC more time to settle.
        printf("I %s\n", sample_set_to_str(1));
        // Turns out that this makes no observable difference.
        break;
    case 'P':
        // Report the selected sample set for the configured channels.
        // An index of 0 refers to the oldest sample set.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume sample index.
            uint32_t ii = (uint32_t) atol(token_ptr);
            printf("P %s\n", sample_set_to_str(ii));
        } else {
            printf("P error: no index given.\n");
        }
        break;
    case 'a':
        // Report index of oldest sample set in data[].
        printf("a %u\n", oldest_fullword_index_in_data() / 4);
        break;
    case 'B':
        // Send the selected sample set as hex-encoded bytes.
        // More efficient than decimal 'P' command, but safe for text transmission.
        // An index of 0 refers to the oldest sample set.
        // Each sample is 4 bytes (int32_t), sent as 8 hex characters (little-endian).
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume sample index.
            uint32_t ii = (uint32_t) atol(token_ptr);
            // Calculate the word index for the selected sample set.
            uint32_t word_index = oldest_fullword_index_in_data() + 4*ii;
            if (word_index >= N_FULLWORDS) { word_index -= N_FULLWORDS; }
            // Send acknowledgment header and hex data
            printf("B ");
            // Send hex-encoded bytes for each channel (4 channels × 8 hex chars = 32 chars total)
            for (uint8_t ch = 0; ch < N_CHAN; ch++) {
                int32_t sample = data[word_index + ch];
                uint8_t* bytes = (uint8_t*)&sample;
                // Send 4 bytes as 8 hex characters (little-endian order)
                for (int b = 0; b < 4; b++) {
                    printf("%02x", bytes[b]);
                }
            }
            printf("\n");
        } else {
            printf("B error: no index given.\n");
        }
        break;
    case 'z':
        // Release the EVENT# line.
        // Presumably this line has been help low following an internal
        // trigger event during the sampling process.
        release_event();
        printf("z Pico2-EVENT line released\n");
        break;
    case 'm':
        // Report the maximum number of sample sets that can be stored in SRAM.
        printf("m %d\n", MAX_N_SAMPLES);
        break;
    case 'T':
        // Report the trigger index (sample number where trigger occurred).
        // This is the fullword index, divide by 4 to get sample number.
        printf("T %u\n", trigger_fullword_index / 4);
        break;
    case '0':
        // Clear the data[N_FULLWORDS] array to all zeros.
        clear_data_array();
        printf("0 data[ ] array cleared\n");
        break;
	default:
		printf("%c error: Unknown command\n", cmdStr[0]);
    }
    if (!override_led) gpio_put(LED_PIN, 0); // To indicate end of interpreter activity.
} // end interpret_command()


int main()
{
	set_registers_to_original_values();
    stdio_init_all();
	uart_set_baudrate(uart0, 230400);
	// Attempt to discard any characters sitting the UART already.
	while (uart_is_readable_within_us(uart0, 100)) {
		__unused char junkc = uart_getc(uart0);
	}
	//
    // Some information for picotool.
	//
    bi_decl(bi_program_description(VERSION_STR));
    bi_decl(bi_1pin_with_name(LED_PIN, "LED output pin"));
    bi_decl(bi_1pin_with_name(FLAG_PIN, "Flag output pin for timing measurements"));
    bi_decl(bi_1pin_with_name(READY_PIN, "Ready/Busy# output pin"));
    bi_decl(bi_1pin_with_name(Pico2_EVENT_PIN, "Pico2 EVENT output pin"));
    bi_decl(bi_1pin_with_name(SYSTEM_EVENTn_PIN, "Sense EVENT input pin"));
    bi_decl(bi_1pin_with_name(DRDYn_PIN, "ADS131M04 DRDYn, input pin"));
    bi_decl(bi_1pin_with_name(SYNCHn_PIN, "ADS131M04 SYNCHn, ouput pin"));
    bi_decl(bi_1pin_with_name(CLKIN_PIN, "ADS131M04 CLKIN, PWM ouput pin"));
    bi_decl(bi_1pin_with_name(SPI1_CSn_PIN, "ADS131M04 chip select, output pin"));
    bi_decl(bi_3pins_with_func(SPI1_RX_PIN, SPI1_TX_PIN, SPI1_CLK_PIN, GPIO_FUNC_SPI));
    bi_decl(bi_1pin_with_name(SPI0_CSn_PIN, "SPI0 slave-select input pin"));
    bi_decl(bi_1pin_with_name(SPI0_SCK_PIN, "SPI0 clock input pin"));
    bi_decl(bi_1pin_with_name(SPI0_TX_PIN, "SPI0 data output pin"));
    bi_decl(bi_1pin_with_name(RTDP_DE_PIN, "RTDP transmit driver enable pin"));
    bi_decl(bi_1pin_with_name(RTDP_REn_PIN, "RTDP read serial-clock enable pin"));
    bi_decl(bi_1pin_with_name(DATA_RDY_PIN, "RTDP data-ready output pin"));
	//
	// Flash LED twice at start up.
	//
    gpio_init(LED_PIN);
    gpio_set_dir(LED_PIN, GPIO_OUT);
	sampling_LED_ON(); sleep_ms(500);
	sampling_LED_OFF(); sleep_ms(500);
	sampling_LED_ON(); sleep_ms(500);
	sampling_LED_OFF();
	//
	// Configure pins to drive the ADS131M04 chip.
	//
    gpio_init(SPI1_CSn_PIN);
    gpio_set_dir(SPI1_CSn_PIN, GPIO_OUT);
    gpio_set_slew_rate(SPI1_CSn_PIN, GPIO_SLEW_RATE_FAST);
    gpio_set_drive_strength(SPI1_CSn_PIN, GPIO_DRIVE_STRENGTH_12MA);
    gpio_put(SPI1_CSn_PIN, 1); // High to deselect.
    //
    // Limit SPI clock to 4MHz for strip-board prototype.
    // Allow higher for Jeremy's PCB.
    spi_init(spi1, 12000*1000);
    spi_set_format(spi1, 8, SPI_CPOL_0, SPI_CPHA_1, SPI_MSB_FIRST);
    gpio_set_function(SPI1_RX_PIN, GPIO_FUNC_SPI);
    gpio_set_function(SPI1_TX_PIN, GPIO_FUNC_SPI);
    gpio_set_slew_rate(SPI1_TX_PIN, GPIO_SLEW_RATE_FAST);
    gpio_set_drive_strength(SPI1_TX_PIN, GPIO_DRIVE_STRENGTH_12MA);
    gpio_set_function(SPI1_CLK_PIN, GPIO_FUNC_SPI);
    gpio_set_slew_rate(SPI1_CLK_PIN, GPIO_SLEW_RATE_FAST);
    gpio_set_drive_strength(SPI1_CLK_PIN, GPIO_DRIVE_STRENGTH_12MA);
    //
    gpio_init(DRDYn_PIN);
    gpio_set_dir(DRDYn_PIN, GPIO_IN);
    //
    gpio_init(SYNCHn_PIN);
    gpio_set_dir(SYNCHn_PIN, GPIO_OUT);
    gpio_set_slew_rate(SYNCHn_PIN, GPIO_SLEW_RATE_FAST);
    gpio_set_drive_strength(SYNCHn_PIN, GPIO_DRIVE_STRENGTH_12MA);
    gpio_put(SYNCHn_PIN, 1); // Idle high.
    //
    // We use PWM slice 4A on GPIO8 (CLKIN_PIN).
    gpio_set_function(CLKIN_PIN, GPIO_FUNC_PWM);
    gpio_set_slew_rate(CLKIN_PIN, GPIO_SLEW_RATE_FAST);
    gpio_set_drive_strength(CLKIN_PIN, GPIO_DRIVE_STRENGTH_12MA);
	//
	// We output an event pin that gets buffered by the COMMS MCU
	// and reflected onto the system event line.
	// We sense that system event line, also.
	//
	gpio_init(Pico2_EVENT_PIN);
	gpio_set_dir(Pico2_EVENT_PIN, GPIO_OUT);
    gpio_disable_pulls(Pico2_EVENT_PIN);
	gpio_init(SYSTEM_EVENTn_PIN);
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_IN);
    gpio_disable_pulls(SYSTEM_EVENTn_PIN);
	release_event();
	//
    gpio_init(FLAG_PIN);
    gpio_set_dir(FLAG_PIN, GPIO_OUT);
    lower_flag_pin();
    sampling_error_flag = 0;
    //
    // Set up the Real-Time Data Port.
    // First, the RS485 transceiver.
    gpio_init(RTDP_DE_PIN);
    gpio_set_dir(RTDP_DE_PIN, GPIO_OUT);
    gpio_disable_pulls(RTDP_DE_PIN);
    gpio_init(RTDP_REn_PIN);
    gpio_set_dir(RTDP_REn_PIN, GPIO_OUT);
    gpio_disable_pulls(RTDP_REn_PIN);
    disable_RTDP_transceiver();
    // Second, the DATA_RDY signal.
    gpio_init(DATA_RDY_PIN);
    gpio_set_dir(DATA_RDY_PIN, GPIO_OUT);
    gpio_disable_pulls(DATA_RDY_PIN);
    clear_data_ready();
    // Third, use the SPI0 module as a slave, for transmit only,
    // but defer its initialization until we need it.
    //
	// Signal to the COMMS MCU that we are ready.
	//
    gpio_init(READY_PIN);
    gpio_set_dir(READY_PIN, GPIO_OUT);
	assert_ready();
    //
	// Enter the command loop.
    while (1) {
        // Characters are not echoed as they are typed.
        // Backspace deleting is allowed.
        // NL (Ctrl-J) signals end of incoming string.
        int m = getstr(bufA, NBUFA);
		m = trim_string(bufA);
        // Note that the cmd string may be of zero length,
        // with the null character in the first place.
        // If that is the case, do nothing with it
		// but just reply with a newline character.
        if (m > 0) {
            interpret_command(bufA);
        } else {
			printf("error: empty command\n");
		}
    }
    return 0;
}
