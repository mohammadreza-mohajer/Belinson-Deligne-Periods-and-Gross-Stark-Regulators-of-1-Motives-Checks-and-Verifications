import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Abel

/-! The monomial kernel used for both numerical and functional relations (Sections 6 and 7).
Taking A = (ι →₀ ℕ) gives the usual polynomial algebra in monomial coordinates. -/
namespace BD.Relations
open AddMonoidAlgebra

variable {k A B : Type*} [CommRing k] [AddCommMonoid A] [AddCommMonoid B]

def fiberIdeal (w : A →+ B) : Ideal (AddMonoidAlgebra k A) :=
  Ideal.span {p | ∃ a b : A, w a = w b ∧
    p = Finsupp.single a (1:k) - Finsupp.single b 1}

theorem binomial_mem (w : A →+ B) {a b : A} (h : w a = w b) :
    Finsupp.single a (1:k) - Finsupp.single b 1 ∈ fiberIdeal w :=
  Ideal.subset_span ⟨a,b,h,rfl⟩

/-- Classifying the entire ideal, allowing torsion in the exponent monoids and
arbitrary commutative coefficient rings. No transcendence premise enters this theorem. -/
theorem kernel_eq_fiberIdeal (w : A →+ B) :
    RingHom.ker (mapDomainRingHom k w) = fiberIdeal w := by
  classical
  apply le_antisymm
  · let rep (b : B) : A := if h : ∃ a, w a = b then h.choose else 0
    have hrep (a : A) : w (rep (w a)) = w a := by
      have hex : ∃ z, w z = w a := ⟨a,rfl⟩
      simp only [rep, dif_pos hex]
      exact hex.choose_spec
    have reduction (f : A →₀ k) :
        (f - Finsupp.mapDomain (rep ∘ w) f : A →₀ k) ∈ fiberIdeal (k:=k) w := by
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
        rw [Finsupp.mapDomain_add, add_sub_add_comm]
        exact (fiberIdeal (k:=k) w).add_mem hf hg
      | single a c =>
        rw [Finsupp.mapDomain_single]
        have hb := binomial_mem (k:=k) w (hrep a).symm
        have hm := Ideal.mul_mem_left (fiberIdeal (k:=k) w)
          (Finsupp.single (0:A) c : AddMonoidAlgebra k A) hb
        simpa [Function.comp_apply, mul_sub, single_mul_single] using hm
    intro f hf
    change Finsupp.mapDomain w f = 0 at hf
    have hr := reduction f
    rw [Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero, sub_zero] at hr
    exact hr
  · apply Ideal.span_le.mpr
    rintro p ⟨a,b,h,rfl⟩
    change Finsupp.mapDomain w (Finsupp.single a (1:k) - Finsupp.single b 1) = 0
    rw [show Finsupp.mapDomain w (Finsupp.single a (1:k) - Finsupp.single b 1) =
      Finsupp.mapDomain w (Finsupp.single a (1:k)) -
        Finsupp.mapDomain w (Finsupp.single b 1) from
      map_sub (Finsupp.mapDomain.addMonoidHom w) _ _]
    simp [h]

/-- Passing to an injective realization of the target does not change any relation.
For normalized values and analytic germs the needed injections are different inputs. -/
theorem realized_kernel {S : Type*} [CommRing S] (w : A →+ B)
    (ev : AddMonoidAlgebra k B →+* S) (hinj : Function.Injective ev) :
    RingHom.ker (ev.comp (mapDomainRingHom k w)) = fiberIdeal w := by
  rw [← kernel_eq_fiberIdeal]
  ext f
  change ev ((mapDomainRingHom k w) f) = 0 ↔ (mapDomainRingHom k w) f = 0
  rw [← ev.map_zero]
  exact hinj.eq_iff

theorem brauer_clear {C : Type*} [AddCancelCommMonoid C] (u v common : C) :
    u + common = v + common ↔ u = v := add_right_cancel_iff

end BD.Relations

