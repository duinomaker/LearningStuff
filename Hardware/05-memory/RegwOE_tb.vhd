library IEEE;
use IEEE.std_logic_1164.all;

entity RegwOE_tb is
end RegwOE_tb;

architecture Behavioral of RegwOE_tb is
  signal len_s : integer := 8;
  signal I_s, Q_s : std_logic_vector(len_s-1 downto 0);
  signal OE_s, Ld_s : std_logic;
  signal Clk_s, Rst_s : std_logic;
begin

  test : entity work.RegwOE(Behavioral)
    generic map (
      len_s)
    port map (
      I_s,
      Q_s,
      OE_s, Ld_s,
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
    I_s <= (others => '0'); 
    OE_s <= '1'; Ld_s <= '0';
    Rst_s <= '1';
    wait until (Clk_s = '1' and Clk_s'event);
    wait for 5 ns;
    Rst_s <= '0';
    wait until (Clk_s = '1' and Clk_s'event);
    wait for 5 ns;
    I_s <= (2 => '1', 1 => '0', 0 => '1', others => '0');
    Ld_s <= '1';
    wait until (Clk_s = '1' and Clk_s'event);
    wait for 5 ns;
    wait;
  end process test_proc;

end Behavioral;
