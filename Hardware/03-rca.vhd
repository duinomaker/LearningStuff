library IEEE;
use IEEE.std_logic_1164.all;

entity ripple_carry_adder is
    generic (
        width : natural := 8
    );
    port (
        A, B  : in  std_logic_vector(width-1 downto 0);
        S     : out std_logic_vector(width-1 downto 0);
        C_in  : in  std_logic;
        C_out : out std_logic
    );
end entity ripple_carry_adder;


architecture Structural of ripple_carry_adder is

    signal C_mid : std_logic_vector(width downto 0);

    component full_adder is
        port (
            A, B, C_in : in  std_logic;
            S, C_out   : out std_logic
        );
    end component full_adder;

begin

    C_mid(0) <= C_in;

    PROPAGATE : for i in 0 to width-1 generate
        U_i : full_adder
            port map (
                A     => A(i),
                B     => B(i),
                C_in  => C_mid(i),
                S     => S(i),
                C_out => C_mid(i+1)
            );
    end generate PROPAGATE;

    C_out <= C_mid(width);

end architecture Structural;
