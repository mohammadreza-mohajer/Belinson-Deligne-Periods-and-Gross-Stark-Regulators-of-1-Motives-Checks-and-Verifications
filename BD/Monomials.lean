import BD.Relations
import BD.GenericDet
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Algebraic independence of monomial families and of generic determinants in
mathlib's standard sense. -/
namespace BD.Monomials
open MvPolynomial AddMonoidAlgebra
variable {K I J : Type*} [CommRing K] [Nontrivial K]

theorem injectiveExponentCriterion {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (w : A →+ B) : Function.Injective (mapDomainRingHom K w) ↔ Function.Injective w := by
  constructor
  · intro h a b hab
    classical
    have he : (Finsupp.single a (1:K) : AddMonoidAlgebra K A)=Finsupp.single b 1 := by
      apply h
      change Finsupp.mapDomain w (Finsupp.single a (1:K)) =
        Finsupp.mapDomain w (Finsupp.single b 1)
      simp [hab]
    by_contra hne
    have hh := DFunLike.congr_fun he a
    simp [Finsupp.single_apply,hne,Ne.symm hne] at hh
  · intro h
    exact Finsupp.mapDomain_injective h

noncomputable def imageVar (w : (I →₀ ℕ) →+ (J →₀ ℕ)) (i : I) : MvPolynomial J K :=
  monomial (w (Finsupp.single i 1)) 1

theorem independence (w : (I →₀ ℕ) →+ (J →₀ ℕ)) :
    AlgebraicIndependent K (imageVar (K:=K) w) ↔ Function.Injective w := by
  have he : aeval (imageVar (K:=K) w) = mapDomainAlgHom K K w := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X]
    change Finsupp.single (w (Finsupp.single i 1)) (1:K) =
      Finsupp.mapDomain w (Finsupp.single (Finsupp.single i 1) (1:K))
    rw [Finsupp.mapDomain_single]
  rw [algebraicIndependent_iff_injective_aeval, he]
  exact injectiveExponentCriterion w

omit [Nontrivial K] in
theorem genericBlockIndependence (d : J → ℕ) :
    AlgebraicIndependent K (fun j => (BD.GenericDet.block (K:=K) d j).det) :=
  algebraicIndependent_iff_injective_aeval.mpr (BD.GenericDet.independentDeterminants d)

end BD.Monomials

