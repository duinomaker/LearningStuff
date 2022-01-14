library IEEE;
use IEEE.std_logic_1164.all;

entity RegFwE is
  generic (
    len_addr : integer;
    len_reg : integer);
  port (
    W_e, R_e : in std_logic;
    W_addr, R_addr : in std_logic_vector(len_addr-1 downto 0);
    W_data : in std_logic_vector(len_reg-1 downto 0);
    R_data : out std_logic_vector(len_reg-1 downto 0);
    Clk, Rst : in std_logic);
end entity;

architecture Structural of RegFwE is
  signal OE, Ld : std_logic_vector(0 to 2**len_addr-1);
begin

  regs : for index in 0 to 2**len_addr-1 generate
    reg : entity work.RegwOE(Behavioral)
      generic map (
        len_reg)
      port map (
        W_data,
        R_data,
        OE(index), Ld(index),
        Clk, Rst);
  end generate;

  W_mux : entity work.MUXwE(Behavioral)
    generic map (
      len_addr)
    port map (
      W_addr,
      Ld,
      W_e);

  R_mux : entity work.MUXwE(behavioral)
    generic map (
      len_addr)
    port map (
      R_addr,
      OE,
      R_e);

end Structural;