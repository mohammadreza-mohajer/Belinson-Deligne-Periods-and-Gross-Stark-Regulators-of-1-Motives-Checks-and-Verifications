import BD.Cubic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum

namespace BD.Cubic
open Set Polynomial
theorem discriminantNotSquare : ¬ IsSquare (229:ℚ) := by
  change ¬IsSquare ((229:ℕ):ℚ)
  rw [Rat.isSquare_natCast_iff]
  decide +kernel

/-- Three disjoint isolating intervals; their existence certifies total reality. -/
theorem threeRealRoots :
    (∃ x ∈ Ioo (-3:ℝ) (-2), (polynomial ℝ).IsRoot x) ∧
    (∃ x ∈ Ioo (0:ℝ) 1, (polynomial ℝ).IsRoot x) ∧
    (∃ x ∈ Ioo (1:ℝ) 2, (polynomial ℝ).IsRoot x) := by
  let f := fun x : ℝ => x^3-4*x+1
  have hc : Continuous f := by dsimp [f]; fun_prop
  have e (t : ℝ) (h : f t=0) : (polynomial ℝ).IsRoot t := by
    simpa [polynomial,Polynomial.IsRoot.def,f] using h
  obtain ⟨x,hx,hf⟩ := intermediate_value_Ioo (f:=f) (a:=(-3:ℝ)) (b:=(-2:ℝ))
    (by norm_num) hc.continuousOn (show 0∈Ioo (f (-3)) (f (-2)) by norm_num [f])
  obtain ⟨y,hy,hg⟩ := intermediate_value_Ioo' (f:=f) (a:=(0:ℝ)) (b:=(1:ℝ))
    (by norm_num) hc.continuousOn (show 0∈Ioo (f 1) (f 0) by norm_num [f])
  obtain ⟨z,hz,hh⟩ := intermediate_value_Ioo (f:=f) (a:=(1:ℝ)) (b:=(2:ℝ))
    (by norm_num) hc.continuousOn (show 0∈Ioo (f 1) (f 2) by norm_num [f])
  exact ⟨⟨x,hx,e _ hf⟩,⟨y,hy,e _ hg⟩,⟨z,hz,e _ hh⟩⟩
end BD.Cubic

