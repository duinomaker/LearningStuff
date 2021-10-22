library IEEE;
use IEEE.std_logic_1164.all;

entity half_adder is
    port (
        A, B : in  std_logic;
        S, C : out std_logic
    );
end entity half_adder;

architecture RTL of half_adder is
begin
    S <= A xor B;
    C <= A and B;
end architecture RTL;

library IEEE;
use IEEE.std_logic_1164.all;

entity full_adder is
    port (
        A, B, C_in : in  std_logic;
        S, C_out   : out std_logic
    );
end entity full_adder;

architecture Structural of full_adder is
    signal S_1, C_1, C_2 : std_logic;
begin
    U1 : entity work.half_adder(RTL)
        port map (
            A, B,
            S_1, C_1
        );
    U2 : entity work.half_adder(RTL)
        port map (
            C_in, S_1,
            S, C_2
        );
    U3 : C_out <= C_1 or C_2;
end architecture Structural;

library IEEE;
use IEEE.std_logic_1164.all;

entity byte_ripple_carry_adder is
    port (
        A, B : in  std_logic_vector(7 downto 0);
        S    : out std_logic_vector(7 downto 0);
        C_in : in  std_logic;
        C    : out std_logic
    );
end entity byte_ripple_carry_adder;

-- I screwed up the propagation direction of carry values.
-- the architecture below would not behave properly.

architecture Structural of byte_ripple_carry_adder is
    signal C_mid : std_logic_vector(7 downto 0);
begin
    C_mid(7) <= C_in;
    U7 : entity work.full_adder(Structural)
        port map (
            A(7), B(7), C_mid(7),
            S(7), C_mid(6)
        );
    U6 : entity work.full_adder(Structural)
        port map (
            A(6), B(6), C_mid(6),
            S(6), C_mid(5)
        );
    U5 : entity work.full_adder(Structural)
        port map (
            A(5), B(5), C_mid(5),
            S(5), C_mid(4)
        );
    U4 : entity work.full_adder(Structural)
        port map (
            A(4), B(4), C_mid(4),
            S(4), C_mid(3)
        );
    U3 : entity work.full_adder(Structural)
        port map (
            A(3), B(3), C_mid(3),
            S(3), C_mid(2)
        );
    U2 : entity work.full_adder(Structural)
        port map (
            A(2), B(2), C_mid(2),
            S(2), C_mid(1)
    );
    U1 : entity work.full_adder(Structural)
        port map (
            A(1), B(1), C_mid(1),
            S(1), C_mid(0)
        );
    U0 : entity work.full_adder(Structural)
        port map (
            A(0), B(0), C_mid(0),
            S(0), C
        );
end architecture Structural;
