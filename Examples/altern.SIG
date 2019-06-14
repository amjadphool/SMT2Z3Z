%alternate (complementing) the signal x %
process ALTERN =
(? boolean a;
! boolean x)
(| x ^= when a 
 | x := not(zx)
 |zx := x$1
 |)
where boolean zx init false;
end;
