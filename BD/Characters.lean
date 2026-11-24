import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-! Repeated regulator blocks and their multiplicities. -/
namespace BD.Characters
open scoped BigOperators
variable {I J K E : Type*} [Fintype I] [Fintype J]

/-- Multiplying normalized regulator coefficients adds their exponent vectors.
The determinant entries may vanish. -/
theorem monomialProduct [CommMonoid K] (d : J → K) (m : I → J → ℕ) (a : I → ℕ) :
    (∏ i, (∏ j, d j ^ m i j)^a i) =
      ∏ j, d j ^ (∑ i, m i j * a i) := by
  simp only [← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  simp only [Finset.prod_pow_eq_pow_sum]

theorem coefficientBinomial [CommMonoid K] (d : J → K) (m : I → J → ℕ) (a b : I → ℕ)
    (h : ∀ j, ∑ i, m i j*a i = ∑ i, m i j*b i) :
    (∏ i, (∏ j, d j^m i j)^a i) = ∏ i, (∏ j, d j^m i j)^b i := by
  rw [monomialProduct,monomialProduct]
  simp only [h]

/-- Pulling back independent affine coordinates along the trace multiplicity matrix. -/
theorem affineTrace [Field K] [Field E] [Algebra K E]
    (v : J → E) (ind : ∀ (b : K) (x : J → K),
      algebraMap K E b + ∑ j, algebraMap K E (x j)*v j = 0 ↔ b=0 ∧ ∀ j,x j=0)
    (m : I → J → K) (b : K) (a : I → K) :
    algebraMap K E b + ∑ i, algebraMap K E (a i)*(∑ j, algebraMap K E (m i j)*v j) = 0 ↔
      b=0 ∧ ∀ j, ∑ i, a i*m i j=0 := by
  have exchange :
      (∑ i, algebraMap K E (a i)*(∑ j, algebraMap K E (m i j)*v j)) =
      ∑ j, algebraMap K E (∑ i, a i*m i j)*v j := by
    simp only [Finset.mul_sum, map_sum, map_mul, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rw [exchange]
  exact ind _ _

theorem liftDimensionBound (m d k : I → ℕ) (h : ∀ i, k i ≤ d i/2) :
    ∑ i, m i*k i ≤ ∑ i, m i*(d i/2) := by
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h i))

omit [Fintype I] in
theorem stabilizerCriterion {G T : Type*} (σ : G → I → I)
    (τ : G → T → T) (v : I → T) (inj : Function.Injective v)
    (equivariance : ∀ g i, τ g (v i) = v (σ g i)) (g : G) (i : I) :
    τ g (v i) = v i ↔ σ g i=i := by rw [equivariance,inj.eq_iff]

/-- A nonzero valuation of a and the nonzero unit logarithm force
both coefficients of a putative rational logarithm relation to vanish. -/
theorem quadraticIndependence [Field K] (v l : K) (hv : v≠0) (hl : l≠0)
    (m n : K) (valuation : m*v=0) (unitLog : m=0 → n*l=0) :
    m=0 ∧ n=0 := by
  have hm := (mul_eq_zero.mp valuation).resolve_right hv
  exact ⟨hm,(mul_eq_zero.mp (unitLog hm)).resolve_right hl⟩

end BD.Characters

