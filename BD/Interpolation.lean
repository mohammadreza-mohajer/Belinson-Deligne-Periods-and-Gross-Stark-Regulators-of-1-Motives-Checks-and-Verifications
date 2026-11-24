import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic

/-! Two cross-realization arguments from the proof of Theorem 7.1.
Row descent works for infinitely many equations. The polynomial argument
works on any sequence along which reciprocals tend to zero. -/
namespace BD.Interpolation
open Filter Topology Polynomial
open scoped BigOperators

/-- A nonzero null vector after scalar extension yields a nonzero null vector
over the original field for the *same* possibly infinite system of rows. -/
theorem descendRows {K E I S : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Fintype I] (row : S → I → K) (c : I → E) (hc : c ≠ 0)
    (h : ∀ s, ∑ i, (row s i) • c i = 0) :
    ∃ b : I → K, b ≠ 0 ∧ ∀ s, ∑ i, row s i*b i = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! hh
    exact hc (funext hh)
  let basis := Basis.ofVectorSpace K E
  have hn : basis.repr (c i) ≠ 0 := fun hh => hi (basis.repr.map_eq_zero_iff.mp hh)
  obtain ⟨j,hj⟩ : ∃ j, basis.repr (c i) j ≠ 0 := by
    by_contra! hz
    exact hn (Finsupp.ext hz)
  let φ := basis.coord j
  refine ⟨fun k => φ (c k), ?_, ?_⟩
  · intro hz
    exact hj (congrFun hz i)
  · intro s
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg φ (h s)

/-- A polynomial that tends to zero on an escaping sequence must vanish.
Stripping the constant term avoids a growth theorem for complex polynomials. -/
theorem escapingPolynomial {K : Type*} [NormedField K] (z : ℕ → K)
    (hn : ∀ᶠ n in atTop, z n ≠ 0) (hinv : Tendsto (fun n => (z n)⁻¹) atTop (𝓝 0))
    (P : K[X]) (hP : Tendsto (fun n => P.eval (z n)) atTop (𝓝 0)) : P=0 := by
  induction hdeg : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hzero : n=0
    · have hC := Polynomial.eq_C_of_natDegree_eq_zero (hdeg.trans hzero)
      have hconst : Tendsto (fun _ : ℕ => P.coeff 0) atTop (𝓝 0) := by
        have hh : Tendsto (fun k => (C (P.coeff 0)).eval (z k)) atTop (𝓝 0) := by
          simpa only [← hC] using hP
        simpa using hh
      have hc : P.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
      rw [hC,hc,map_zero]
    · have hsub := (hP.sub (tendsto_const_nhds (x := P.coeff 0))).mul hinv
      have hlim : Tendsto (fun n => P.divX.eval (z n)) atTop (𝓝 0) := by
        have hlim' : Tendsto (fun k => (P.eval (z k) - P.coeff 0) * (z k)⁻¹) atTop (𝓝 0) := by
          simpa using hsub
        apply hlim'.congr'
        filter_upwards [hn] with k hk
        have hid := congrArg (fun Q : K[X] => Q.eval (z k)) P.divX_mul_X_add
        simp only [eval_add, eval_mul, eval_X, eval_C] at hid
        rw [← hid,add_sub_cancel_right,mul_assoc,mul_inv_cancel₀ hk,mul_one]
      have hlt : P.divX.natDegree<n := by
        rw [natDegree_divX_eq_natDegree_tsub_one,hdeg]; omega
      have hd := ih _ hlt P.divX hlim rfl
      have hC : P = C (P.coeff 0) := by simpa [hd] using P.divX_mul_X_add.symm
      have hconst : Tendsto (fun _ : ℕ => P.coeff 0) atTop (𝓝 0) := by
        have hh : Tendsto (fun k => (C (P.coeff 0)).eval (z k)) atTop (𝓝 0) := by
          simpa only [← hC] using hP
        simpa using hh
      have hc : P.coeff 0=0 := tendsto_nhds_unique tendsto_const_nhds hconst
      rw [hC,hc,map_zero]

/-- After dividing a relation by its largest surviving frequency,
the smaller-frequency tail tends to zero and the leading polynomial vanishes. -/
theorem leadingFrequency {K : Type*} [NormedField K] (z tail : ℕ → K)
    (hn : ∀ᶠ n in atTop, z n≠0) (hinv : Tendsto (fun n => (z n)⁻¹) atTop (𝓝 0))
    (P : K[X]) (ht : Tendsto tail atTop (𝓝 0))
    (cancel : ∀ᶠ n in atTop, P.eval (z n)+tail n=0) : P=0 := by
  apply escapingPolynomial z hn hinv
  have hneg : Tendsto (fun k => -(tail k)) atTop (𝓝 0) := by simpa using ht.neg
  apply hneg.congr'
  filter_upwards [cancel] with n h
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem factorialDominates (c : ℝ) (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => c^(k j) / (k j).factorial) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial c).tendsto_atTop_zero.comp hk

end BD.Interpolation

