% and or and not gate for previous value and a input%
process andornotgate =
(? boolean a, clk;
! boolean x, y ,z)
(| x ^=y ^=z ^=a ^=when clk
 | x := not(zx)
 | y := zy or a
 | z := zz and a
 |zx := x$1 init false
 |zy := y$1 init true
 |zz := z$1 init false
 |)
where boolean zx, zy , zz;
end;
