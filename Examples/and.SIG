% and gate for previous value and a input%
process andgate =
(? boolean a, clk;
! boolean x)
(| x ^=a ^=when clk
 | x := zx and a
 |zx := x$1
 |)
where boolean zx init false;
end;
