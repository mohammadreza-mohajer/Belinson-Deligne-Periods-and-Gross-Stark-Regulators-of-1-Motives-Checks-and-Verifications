import BD.Arithmetic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

namespace BD.Cubic
open Polynomial
noncomputable def polynomial (R : Type*) [CommRing R] : R[X] :=
  X^3 - C (4:R)*X + 1

theorem noRationalRoot (q : ℚ) : ¬ (polynomial ℚ).IsRoot q := by
  intro h
  have hm : (polynomial ℤ).Monic := by unfold polynomial; monicity!
  have val : aeval q (polynomial ℤ) = 0 := by
    simp only [polynomial, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
    norm_num [polynomial, Polynomial.IsRoot.def] at h ⊢
    exact h
  obtain ⟨z,hq,hdiv⟩ := exists_integer_of_is_root_of_monic hm val
  have h0 : (polynomial ℤ).coeff 0 = 1 := by simp [polynomial]
  rw [h0] at hdiv
  have hz : z=1 ∨ z = -1 := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hdiv)
  rcases hz with rfl | rfl <;> subst q <;> norm_num [polynomial,Polynomial.IsRoot.def] at h

theorem irreducible : Irreducible (polynomial ℚ) := by
  have hdeg : (polynomial ℚ).natDegree=3 := by unfold polynomial; compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdeg]
  · exact noRationalRoot

/-- Identity of polynomials, stronger than agreement at the seven residues. -/
theorem factorSeven : polynomial (ZMod 7) =
    (X-C 4)*(X^2+C 4*X+C 5) := by
  unfold polynomial
  have h1 : (-(20:ZMod 7))=1 := by decide
  have h2 : ((5:ZMod 7)-16) = -4 := by decide
  calc
    _ = X^3+C ((5:ZMod 7)-16)*X+C (-(20:ZMod 7)) := by rw [h1,h2]; simp; ring
    _ = _ := by
      rw [show (16:ZMod 7)=4^2 by decide, show (20:ZMod 7)=4*5 by decide,
        map_sub,map_neg,map_mul,map_pow]
      ring

end BD.Cubic

