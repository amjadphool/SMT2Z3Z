% or gate for previous value and a input%
process orgate =
(? boolean a, clk;
! boolean x)
(| x ^=a ^=when clk
 | x := zx or a
 |zx := x$1
 |)
where boolean zx init false;
end;
