library IEEE;
use IEEE.std_logic_1164.all;

entity MUXwE_tb is
end MUXwE_tb;

architecture Behavioral of MUXwE_tb is
  signal len_s : integer := 2;
  signal I_s : std_logic_vector(len_s-1 downto 0);
  signal O_s : std_logic_vector(2**len_s-1 downto 0);
  signal E_s : std_logic;
begin

  test : entity work.MUXwE(Behavioral)
    generic map (
      len_s)
    port map (
      I_s,
      O_s,
      E_s);
  
  test_proc : process
  begin
    E_s <= '1';
    I_s <= "00";
    wait for 10 ns;
    I_s <= "01";
    wait for 10 ns;
    I_s <= "10";
    wait for 10 ns;
    I_s <= "11";
    wait;
  end process test_proc;

end Behavioral;