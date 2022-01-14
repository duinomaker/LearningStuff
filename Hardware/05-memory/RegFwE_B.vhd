library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;

architecture Behavioral of RegFwE is
  type regfile_type is array(0 to 2**len_addr-1) of
    std_logic_vector(len_reg-1 downto 0);
  signal regfile : regfile_type;
begin

  write_proc : process (Clk)
  begin
    if (Clk = '1' and Clk'event) then
      if (Rst = '1') then
        for index in 0 to 2**len_addr-1 loop
          regfile(index) <= (others => '0');
        end loop;
      elsif (W_e = '1') then
        regfile(conv_integer(unsigned(W_addr))) <= W_data;
      end if;
    end if;
  end process write_proc;
  
  read_proc : process (regfile, R_addr, R_e)
  begin
    if (R_e = '1') then
      R_data <= regfile(conv_integer(unsigned(R_addr)));
    else
      R_data <= (others => 'Z');
    end if;
  end process read_proc;

end Behavioral;