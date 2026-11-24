import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import BD.Characters

/-! Field-generation step of Corollary 6.7 in an actual finite Galois extension. -/
namespace BD.CoefficientField
open IntermediateField
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem fixesGenerators (S : Set E) (σ : E ≃ₐ[K] E) :
    σ∈(adjoin K S).fixingSubgroup ↔ ∀ x ∈ S, σ x=x := by
  change (∀ x : adjoin K S, σ (x:E) = (x:E)) ↔ _
  constructor
  · intro h x hx
    exact h ⟨x,subset_adjoin K S hx⟩
  · intro h x
    apply adjoin_induction K (p:=fun z _ => σ z=z) (fun a ha => h a ha)
      (fun k => σ.commutes k) _ _ _ x.property
    · intro a b _ _ ha hb; rw [map_add,ha,hb]
    · intro a _ ha; rw [map_inv₀,ha]
    · intro a b _ _ ha hb; rw [map_mul,ha,hb]

theorem fieldOfTrace [FiniteDimensional K E] [IsGalois K E]
    {C : Type*} (trace : E) (χ : C → E)
    (h : ∀ σ : E ≃ₐ[K] E, σ trace=trace ↔ ∀ c,σ (χ c)=χ c) :
    adjoin K ({trace} : Set E) = adjoin K (Set.range χ) := by
  have he : (adjoin K ({trace} : Set E)).fixingSubgroup =
      (adjoin K (Set.range χ)).fixingSubgroup := by
    ext σ
    simp only [fixesGenerators,Set.mem_singleton_iff,forall_eq,Set.forall_mem_range]
    exact h σ
  calc
    _ = fixedField (adjoin K ({trace} : Set E)).fixingSubgroup :=
      (IsGalois.fixedField_fixingSubgroup _).symm
    _ = fixedField (adjoin K (Set.range χ)).fixingSubgroup := congrArg fixedField he
    _ = _ := IsGalois.fixedField_fixingSubgroup _

end BD.CoefficientField

