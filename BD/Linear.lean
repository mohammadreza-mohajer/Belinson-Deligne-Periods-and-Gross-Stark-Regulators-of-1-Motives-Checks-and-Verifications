import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-! Norms on divisor spaces, critical projections, and comparison determinants. -/
namespace BD.Linear
open scoped BigOperators
open Module Matrix
variable {K U D V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup D] [Module K D]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Norm correction in the relative S-unit sequence. The section preserves vanishing divisors. -/
theorem relativeLift (v : U →ₗ[K] D) (N : U →ₗ[K] V) (dN : D →ₗ[K] W)
    (v₀ : V →ₗ[K] W) (i : V →ₗ[K] U) (surj : Function.Surjective v)
    (compat : ∀ u, v₀ (N u) = dN (v u)) (sectionN : ∀ z, N (i z) = z)
    (units : ∀ z, v₀ z = 0 → v (i z) = 0) (d : D) (hd : dN d = 0) :
    ∃ u : U, N u = 0 ∧ v u = d := by
  obtain ⟨u,hu⟩ := surj d
  refine ⟨u-i (N u), ?_, ?_⟩
  · simp [sectionN]
  · have h₀ : v₀ (N u) = 0 := by rw [compat,hu,hd]
    simp [units _ h₀,hu]

/-- Surjectivity of the real split projection forces the divisor rank bound.
At equality the divisor projection is injective and both maps have the same kernel. -/
theorem criticalProjection [FiniteDimensional K D] [FiniteDimensional K V]
    (v : U →ₗ[K] D) (p : D →ₗ[K] V) (h : Function.Surjective (p.comp v)) :
    finrank K V ≤ finrank K D ∧
      (finrank K D = finrank K V → LinearMap.ker (p.comp v) = LinearMap.ker v) := by
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨x,hx⟩ := h z
    exact ⟨v x,hx⟩
  constructor
  · have hd := p.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp,finrank_top] at hd
    omega
  · intro he
    have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr hp
    ext x
    change p (v x) = 0 ↔ v x=0
    rw [← p.map_zero]
    exact hi.eq_iff

/-- The information lost on discarding local constituents is the dimension of the kernel. -/
theorem projectionLoss [FiniteDimensional K U] (p : U →ₗ[K] D) :
    finrank K U - finrank K (LinearMap.range p) = finrank K (LinearMap.ker p) := by
  have h := p.finrank_range_add_finrank_ker
  omega

/-- The finite block determinant is valid even when one diagonal comparison is singular. -/
theorem extensionDet {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (fromBlocks A B 0 D).det = A.det * D.det := det_fromBlocks_zero₂₁ A B D

theorem extensionCharpoly {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (fromBlocks A B 0 D).charpoly = A.charpoly * D.charpoly :=
  Matrix.charpoly_fromBlocks_zero₂₁ _ _ _

/-- Multiplicativity of rational determinant classes. -/
def SamePeriod {E : Type*} [Field E] [Algebra ℚ E] (x y : E) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ x = algebraMap ℚ E q * y

theorem periodProduct {E : Type*} [Field E] [Algebra ℚ E] {x y u v : E}
    (h : SamePeriod x y) (g : SamePeriod u v) : SamePeriod (x*u) (y*v) := by
  obtain ⟨a,ha,rfl⟩ := h
  obtain ⟨b,hb,rfl⟩ := g
  refine ⟨a*b,mul_ne_zero ha hb,?_⟩
  rw [map_mul]
  ac_rfl

/-- Cancellation of the two residue factors, with zero numerator permitted. -/
theorem residueQuotient {E : Type*} [Field E] (e f a b x y : E)
    (he : e ≠ 0) (hf : f ≠ 0) (hb : b ≠ 0) (hy : y ≠ 0) :
    ((e*a*x)/(f*b*y))*(f/e) = (a/b)*(x/y) := by field_simp; ac_rfl

end BD.Linear

