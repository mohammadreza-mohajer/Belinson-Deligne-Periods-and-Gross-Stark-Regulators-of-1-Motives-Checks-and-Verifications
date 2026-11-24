import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Linear consequences of the realizations. Realization-specific identifications
enter as separate hypotheses in the paper correspondence. -/
namespace BD.Realizations
open LinearMap
variable {K U D W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup D] [Module K D] [AddCommGroup W] [Module K W]

theorem inertiaKernel (v : U →ₗ[K] D) (tame : D →ₗ[K] W) (ht : Function.Injective tame) :
    ker (tame.comp v) = ker v := by
  ext x
  change tame (v x) = 0 ↔ v x=0
  rw [← tame.map_zero,ht.eq_iff]

/-- An even logarithm kernel meets the odd subspace trivially in characteristic zero. -/
theorem oddLogKernel [CharZero K] (j : U →ₗ[K] U) (l : U →ₗ[K] D)
    (even : ∀ x, l x=0 → j x=x) (x : U) (odd : j x = -x) (hl : l x=0) : x=0 := by
  have hh : x = -x := (even x hl).symm.trans odd
  have h2 : (2:K) • x=0 := by rw [two_smul,hh]; simpa using congrArg (fun y => -x + y) hh.symm
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem affineEvaluation {E : Type*} [Field E] [Algebra K E] (L : U →ₗ[K] E)
    (inj : Function.Injective L)
    (disjoint : ∀ b : K, ∀ u : U, algebraMap K E b = L u → b=0)
    (b : K) (u : U) : algebraMap K E b + L u=0 ↔ b=0 ∧ u=0 := by
  constructor
  · intro h
    have heq : algebraMap K E b = L (-u) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h
    have hb := disjoint b (-u) heq
    refine ⟨hb,inj ?_⟩
    simpa [hb] using h
  · rintro ⟨rfl,rfl⟩
    simp

/-- In the split archimedean diagram the abelian summand cancels from the cokernel. -/
theorem splitRange (t : U →ₗ[K] D) (a : W ≃ₗ[K] W) (d : D) (w : W) :
    (∃ x : U × W, (t x.1,a x.2)=(d,w)) ↔ d∈range t := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨x.1,congrArg Prod.fst h⟩
  · rintro ⟨u,rfl⟩
    exact ⟨(u,a.symm w),by simp⟩

theorem normRatio {x : ℚ} (a b : ℚ) (ha : a≠0) (hb : b≠0) (h : x=a/b) :
    x*(b/a)=1 := by rw [h]; field_simp

end BD.Realizations

