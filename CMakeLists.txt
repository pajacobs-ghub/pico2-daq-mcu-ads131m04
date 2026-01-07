# == DO NOT EDIT THE FOLLOWING LINES for the Raspberry Pi Pico VS Code Extension to work ==
if(WIN32)
    set(USERHOME $ENV{USERPROFILE})
else()
    set(USERHOME $ENV{HOME})
endif()
set(sdkVersion 2.2.0)
set(toolchainVersion 14_2_Rel1)
set(picotoolVersion 2.2.0-a4)
set(picoVscode ${USERHOME}/.pico-sdk/cmake/pico-vscode.cmake)
if (EXISTS ${picoVscode})
    include(${picoVscode})
endif()
# ====================================================================================
cmake_minimum_required(VERSION 3.18)
set(PICO_BOARD pico2)

if (DEFINED ENV{PICO_SDK_PATH} AND (NOT PICO_SDK_PATH))
    set(PICO_SDK_PATH $ENV{PICO_SDK_PATH})
    message("Using PICO_SDK_PATH from environment ('${PICO_SDK_PATH}')")
endif ()

set(PICO_SDK_INIT_CMAKE_FILE ${PICO_SDK_PATH}/pico_sdk_init.cmake)
include(${PICO_SDK_INIT_CMAKE_FILE})
message("Raspberry Pi Pico SDK version is ${PICO_SDK_VERSION_STRING}")

project(pico2_daq_ads131m04 C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
# Initialize the SDK
pico_sdk_init()

add_compile_options(-Wall
        -Wno-format # int != int32_t because gcc has int32_t as long int
        )

add_executable(pico2_daq_ads131m04)

target_sources(pico2_daq_ads131m04 PRIVATE pico2_daq_ads131m04.c)

# pull in common dependencies
target_link_libraries(pico2_daq_ads131m04 PRIVATE
	pico_stdlib
    pico_multicore
    pico_util
	hardware_timer
	hardware_spi
    hardware_pwm
    hardware_dma
	)

# enable uart0
pico_enable_stdio_uart(pico2_daq_ads131m04 1)

# create map/bin/hex file etc.
pico_add_extra_outputs(pico2_daq_ads131m04)

# add url via pico_set_program_url
pico_set_program_url(pico2_daq_ads131m04 "https://github.com/pajacobs-ghub/pico2-daq-mcu-ads131m04/")

