# N18 - PL_CLK_50M
# P16 - PL_KEY_1
# P15 - PL_LED_1
# U12 - PL_LED_2

# clocks
create_clock -period 20.000 [get_ports clk]
set_property PACKAGE_PIN N18 [get_ports clk]
set_property IOSTANDARD LVCMOS33 [get_ports clk]

# keys
set_property PACKAGE_PIN P16 [get_ports rst_n]
set_property IOSTANDARD LVCMOS33 [get_ports rst_n]

# LEDs
set_property PACKAGE_PIN P15 [get_ports {led[0]}]
set_property PACKAGE_PIN U12 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[*]}]
