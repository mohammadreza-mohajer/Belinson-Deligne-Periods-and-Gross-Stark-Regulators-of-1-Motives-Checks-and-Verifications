import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FieldSimp

/-! Polynomial separation of character tuples, the last Chebotarev step of Theorem 7.1. -/
namespace BD.Separation
open scoped BigOperators
open MvPolynomial
variable {K I C : Type*} [Field K] [Fintype I]

/-- Every finite set of distinct tuples over a field admits an interpolating delta polynomial. -/
theorem separator (x : I → C → K) (hx : Function.Injective x) (i : I) :
    ∃ P : MvPolynomial C K, (eval (x i) P = 1) ∧ ∀ j, j ≠ i → eval (x j) P = 0 := by
  classical
  have sep (j : {j : I // j ≠ i}) : ∃ c, x i c ≠ x j c := by
    by_contra! h
    exact j.property ((hx (funext h)).symm)
  choose c hc using sep
  let factor (j : {j : I // j ≠ i}) : MvPolynomial C K :=
    MvPolynomial.C ((x i (c j) - x j (c j))⁻¹) *
      ((X (c j) : MvPolynomial C K) - MvPolynomial.C (σ:=C) (x j (c j)))
  refine ⟨∏ j, factor j, ?_, ?_⟩
  · rw [map_prod]
    apply Finset.prod_eq_one
    intro j _
    simp [factor, sub_ne_zero.mpr (hc j)]
  · intro j hj
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨j,hj⟩ : {j : I // j ≠ i}))
    simp [factor]

/-- If the character moments of all monomials vanish, every weight vanishes.
There is no bound on the number of conjugacy classes or tuples. -/
theorem moments_separate (x : I → C → K) (hx : Function.Injective x) (a : I → K)
    (mom : ∀ d : C →₀ ℕ, ∑ i, a i * d.prod (fun c n => x i c ^ n) = 0) :
    ∀ i, a i = 0 := by
  classical
  have allpoly (P : MvPolynomial C K) : ∑ i, a i * eval (x i) P = 0 := by
    induction P using MvPolynomial.induction_on' with
    | monomial d b =>
      simp only [eval_monomial]
      calc
        _ = b * (∑ i, a i * d.prod (fun c n => x i c ^ n)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ac_rfl
        _ = 0 := by rw [mom, mul_zero]
    | add f g hf hg => simp [mul_add, Finset.sum_add_distrib, hf, hg]
  intro i
  obtain ⟨P,hone,hzero⟩ := separator x hx i
  have h := allpoly P
  rw [Finset.sum_eq_single i, hone, mul_one] at h
  · exact h
  · intro j _ hji
    rw [hzero j hji, mul_zero]
  · simp

/-- A common scalar multiplier can be removed from separated weights. -/
theorem weighted_moments (x : I → C → K) (hx : Function.Injective x)
    (a w : I → K) (hw : ∀ i, w i ≠ 0)
    (mom : ∀ d : C →₀ ℕ, ∑ i, (w i * a i) * d.prod (fun c n => x i c ^ n) = 0) :
    ∀ i, a i = 0 := by
  intro i
  exact (mul_eq_zero.mp (moments_separate x hx _ mom i)).resolve_left (hw i)

end BD.Separation

