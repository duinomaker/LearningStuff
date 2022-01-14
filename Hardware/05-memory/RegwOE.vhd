library IEEE;
use IEEE.std_logic_1164.all;

entity RegwOE is
  generic (
    len : integer);
  port (
    I: in std_logic_vector(len-1 downto 0);
    Q : out std_logic_vector(len-1 downto 0);
    OE, Ld : in std_logic;
    Clk, Rst : in std_logic);
end entity;

architecture Behavioral of RegwOE is
  signal R : std_logic_vector(len-1 downto 0);
begin

  reg_proc : process (Clk)
  begin
    if (Clk = '1' and Clk'event) then
      if (Rst = '1') then
        R <= (others => '0');
      elsif (Ld = '1') then
        R <= I;
      end if;
    end if;
  end process reg_proc;

  output_proc : process (R, OE)
  begin
    if (OE = '1') then
      Q <= R;
    else
      Q <= (others => 'Z');
    end if;
  end process output_proc;

end Behavioral;