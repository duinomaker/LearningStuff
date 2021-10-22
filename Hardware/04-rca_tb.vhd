library IEEE;
use IEEE.std_logic_1164.all;

entity ripple_carry_adder_tb is
end entity ripple_carry_adder_tb;


architecture Behavioral of ripple_carry_adder_tb is

    constant width_tb : natural := 2;
    signal A_tb, B_tb, S_tb  : std_logic_vector(width_tb-1 downto 0);
    signal C_in_tb, C_out_tb : std_logic;

    component ripple_carry_adder is
        generic (
            width : natural
        );
        port (
            A, B  : in  std_logic_vector(width-1 downto 0);
            S     : out std_logic_vector(width-1 downto 0);
            C_in  : in  std_logic;
            C_out : out std_logic
        );
    end component ripple_carry_adder;

begin
    -- Instantiate the unit under test (UUT)
    UUT : ripple_carry_adder
        generic map (
            width => width_tb
        )
        port map (
            A     => A_tb,
            B     => B_tb,
            S     => S_tb,
            C_in  => C_in_tb,
            C_out => C_out_tb
        );

    C_in_tb <= '0';

    process is
    begin
        A_tb <= "00";
        B_tb <= "01";
        wait for 10 ns;
        A_tb <= "10";
        B_tb <= "01";
        wait for 10 ns;
        A_tb <= "01";
        B_tb <= "11";
        wait for 10 ns;
        A_tb <= "11";
        B_tb <= "11";
        wait for 10 ns;
    end process;

end architecture Behavioral;
