library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;

entity MUXwE is
  generic (
    len : integer);
  port (
    I : in  std_logic_vector(len-1 downto 0);
    O : out std_logic_vector(2**len-1 downto 0);
    E : in  std_logic);
end MUXwE;

architecture Behavioral of MUXwE is
begin

  process (I, E)
  begin
    if (E = '1') then
      O <= (conv_integer(unsigned(I)) => '1', others => '0');
    else
      O <= (others => '0');
    end if;
  end process;

end Behavioral;
