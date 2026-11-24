import BD.Legendre
import BD.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.Ring

/-! Direct comparison with mathlib's Bernoulli polynomials in the two special
values used by Proposition 8.2. -/
namespace BD.SpecialValues
open Polynomial BD.Arithmetic

private theorem fifth : bernoulli' 5=0 :=
  bernoulli'_odd_eq_zero (by decide) (by decide)
private theorem seventh : bernoulli' 7=0 :=
  bernoulli'_odd_eq_zero (by decide) (by decide)
private theorem sixth : bernoulli' 6=1/42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, fifth]

theorem firstPolynomial (x : ℚ) : (Polynomial.bernoulli 1).eval x = x-1/2 := by
  norm_num [Polynomial.bernoulli,Finset.sum_range_succ,Polynomial.eval_monomial]
  ring

theorem seventhPolynomial (x : ℚ) :
    (Polynomial.bernoulli 7).eval x = x^7-(7/2)*x^6+(7/2)*x^5-(7/6)*x^3+(1/6)*x := by
  norm_num [Polynomial.bernoulli,Finset.sum_range_succ,Polynomial.eval_monomial,
    _root_.bernoulli, Nat.choose, fifth, sixth, seventh]
  ring

/-- The finite expression on the right side of the generalized Bernoulli value formula. -/
noncomputable def bernoulliValue (k : ℕ) : ℚ :=
  -(687:ℚ)^(k-1)/k * ((List.range 687).map (fun i =>
    (delta (i+1) : ℚ) * (Polynomial.bernoulli k).eval ((i+1:ℚ)/687))).sum

set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem actualFirstValue : bernoulliValue 1 = 12 := by
  simp only [bernoulliValue,firstPolynomial]
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem actualSeventhValue : bernoulliValue 7 = -10344805682225424 := by
  simp only [bernoulliValue,seventhPolynomial]
  decide +kernel

end BD.SpecialValues

