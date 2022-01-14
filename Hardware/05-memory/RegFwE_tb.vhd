library IEEE;
use IEEE.std_logic_1164.all;

entity RegFwE_tb is
end entity;

architecture Behavioral of RegFwE_tb is
  signal len_addr : integer := 4;
  signal len_reg : integer := 8;

  signal W_e_s, R_e_s : std_logic;
  signal W_addr_s, R_addr_s : std_logic_vector(len_addr-1 downto 0);
  signal W_data_s, R_data_s : std_logic_vector(len_reg-1 downto 0);
  signal Clk_s, Rst_s : std_logic;
begin

  -- Replace `Structural' to `Behavioral' on the next line to test the
  -- architecture defined in `RedFwE_B.vhd'.
  reg : entity work.RegFwE(Structural)
    generic map (
      len_addr,
      len_reg)
    port map (
      W_e_s, R_e_s,
      W_addr_s, R_addr_s,
      W_data_s,
      R_data_s,
      Clk_s, Rst_s);

  clock_proc : process
  begin
    Clk_s <= '0';
    wait for 10 ns;
    Clk_s <= '1';
    wait for 10 ns;
  end process clock_proc;

  test_proc : process
  begin
    W_e_s <= '1'; R_e_s <= '0';
    W_addr_s <= "0000";
    R_addr_s <= "0000";
    W_data_s <= "10101010";
    Rst_s <= '1';
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    Rst_s <= '0';
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    W_addr_s <= "1010";
    W_data_s <= "01010101";
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    W_e_s <= '0'; R_e_s <= '1';
    R_addr_s <= "1111";
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    assert R_data_s = "00000000"
      report "failed - resetted reg should be zero";
    R_addr_s <= "1010";
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    assert R_data_s = "01010101"
      report "failed - reading reg - 1";
    R_addr_s <= "0000";
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    assert R_data_s = "10101010"
      report "failed - reading reg - 2";
    R_e_s <= '0';
    wait until Clk_s = '1' and Clk_s'event;
    wait for 5 ns;
    assert R_data_s = "ZZZZZZZZ"
      report "failed - reg should be hi-impedance when ^R_e";
    wait;
  end process test_proc;

end Behavioral;