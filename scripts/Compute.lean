import BD.Arithmetic
import BD.Bernoulli
import BD.Examples

/-! Machine-readable scalar report. Exact rationals are emitted through their numerator
and denominator to avoid host numerical conversions. -/
open BD.Arithmetic
def main : IO Unit := do
  IO.println s!"conductor={687}"
  IO.println s!"character_at_p={delta 7}"
  for k in [0,1,3,5,6,7] do IO.println s!"sum_{k}={powerSum k}"
  IO.println s!"L_0={(specialValue 0).num}"
  for n in [6,12,42] do
    let l := specialValue n
    let q := secant n
    IO.println s!"L_minus_{n}_num={l.num}"
    IO.println s!"L_minus_{n}_den={l.den}"
    IO.println s!"secant_{n}_num={q.num}"
    IO.println s!"secant_{n}_den={q.den}"
    IO.println s!"secant_{n}_mod49_ok={slopeResidue n}"
  IO.println s!"F_0={2*(specialValue 0).num}"
  IO.println s!"F_minus_6_mod49={((1+7^6)*(specialValue 6).num)%49}"
  IO.println s!"slope_F={((3-24:Int)*8)%49}"
  IO.println s!"slope_normalized={((28:Int)*47)%49}"
  IO.println s!"cubic_7_roots={roots 7 cubic}"
  IO.println s!"cubic_29_roots={roots 29 cubic}"
  IO.println s!"quadratic_11_roots={roots 11 (fun x => x^2-5)}"
  IO.println s!"quadratic_7_roots={roots 7 (fun x => x^2+3)}"
  IO.println s!"quadratic_29_roots={roots 29 (fun x => x^2+1)}"
  IO.println s!"quadratic_229_at_29={roots 29 (fun x => x^2-229)}"
  IO.println s!"mu3_at_29={roots 29 (fun x => x^2+x+1)}"
  IO.println s!"fixed_dimensions={[BD.Examples.trivial,BD.Examples.sign,BD.Examples.standard,BD.Examples.permThree,BD.Examples.regular].map BD.Examples.fixedDim}"

