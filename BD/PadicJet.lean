import BD.Jet
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Convergent power series on the open unit ball of the actual p-adic integers.
The reduction modulo p² follows from a factorization of the infinite sum. -/
namespace BD.PadicJet
open Filter
open scoped BigOperators Topology
variable {p : ℕ} [Fact p.Prime]

noncomputable def value (a : ℕ → ℤ_[p]) (t : ℤ_[p]) : ℤ_[p] :=
  ∑' n, a n * t^n

theorem integralSeriesSummable (a : ℕ → ℤ_[p]) {t : ℤ_[p]} (ht : (p:ℤ_[p]) ∣ t) :
    Summable (fun n => a n * t^n) := by
  have hlt := (PadicInt.norm_lt_one_iff_dvd t).mpr ht
  apply Summable.of_norm_bounded (fun n : ℕ => ‖t‖^n)
    (summable_geometric_of_lt_one (norm_nonneg t) hlt)
  intro n
  calc
    ‖a n * t^n‖ ≤ ‖a n‖ * ‖t‖^n := by rw [← norm_pow]; exact norm_mul_le _ _
    _ ≤ 1 * ‖t‖^n := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (by positivity)
    _ = _ := one_mul _

/-- The entire tail after the linear term is a multiple of the square of the argument. -/
theorem splitValue (a : ℕ → ℤ_[p]) {t : ℤ_[p]} (ht : (p:ℤ_[p]) ∣ t) :
    value a t = a 0 + a 1*t + t^2 * value (fun n => a (n+2)) t := by
  have hsum := (integralSeriesSummable a ht).sum_add_tsum_nat_add 2
  change (∑' n, a n*t^n) = _
  rw [← hsum]
  have tail : (∑' n : ℕ, a (n+2)*t^(n+2)) = t^2 * value (fun n => a (n+2)) t := by
    unfold value
    rw [← (integralSeriesSummable (fun n => a (n+2)) ht).tsum_mul_left (t^2)]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [tail]
  simp [Finset.sum_range_succ]

/-- The analytic difference quotient in the power-series coordinate tends to the linear
coefficient. The argument ranges over the punctured integral neighbourhood in ℚ_p. -/
theorem differenceQuotient (a : ℕ → ℤ_[p]) :
    Tendsto (fun t : ℤ_[p] => ((value a t - a 0 : ℤ_[p]) : ℚ_[p]) / (t : ℚ_[p]))
      (𝓝[≠] (0 : ℤ_[p])) (𝓝 (a 1 : ℚ_[p])) := by
  let tail := fun t : ℤ_[p] => value (fun n => a (n+2)) t
  have hn : Tendsto (fun t : ℤ_[p] => ‖t‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℤ_[p]))
  have hh : Tendsto (fun t : ℤ_[p] => t*tail t) (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ hn
    intro t
    calc
      ‖t*tail t‖ ≤ ‖t‖ * ‖tail t‖ := norm_mul_le _ _
      _ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖t‖ := mul_one _
  have hs : Tendsto (fun t : ℤ_[p] => a 1 + t*tail t) (𝓝 0) (𝓝 (a 1)) := by
    simpa using (tendsto_const_nhds (x:=a 1)).add hh
  have hc : Continuous (fun t : ℤ_[p] => (t : ℚ_[p])) := continuous_subtype_val
  apply ((hc.tendsto _).comp (hs.mono_left nhdsWithin_le_nhds)).congr'
  have small : ∀ᶠ t : ℤ_[p] in 𝓝 0, ‖t‖ < 1 := hn.eventually_lt_const zero_lt_one
  filter_upwards [self_mem_nhdsWithin,small.filter_mono nhdsWithin_le_nhds] with t hnz ht
  have hne : t ≠ 0 := hnz
  have hne' : (t : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hne
  symm
  apply (div_eq_iff hne').mpr
  rw [splitValue a ((PadicInt.norm_lt_one_iff_dvd t).mp ht)]
  change _ = ((a 1 + t*value (fun n => a (n+2)) t : ℤ_[p]) : ℚ_[p]) * _
  push_cast
  ring

/-- Reduction of a convergent integral series computes its first jet at any p-divisible input. -/
theorem reduceValue (a : ℕ → ℤ_[p]) {t : ℤ_[p]} (ht : (p:ℤ_[p]) ∣ t) :
    PadicInt.toZModPow 2 (value a t) =
      PadicInt.toZModPow 2 (a 0) + PadicInt.toZModPow 2 (a 1) * PadicInt.toZModPow 2 t := by
  let ρ := (PadicInt.toZModPow 2 : ℤ_[p] →+* ZMod (p^2))
  have zeroSq : ρ t ^ 2 = 0 := by
    obtain ⟨u,hu⟩ := ht
    rw [hu,map_mul,mul_pow,map_natCast]
    have hz : (p : ZMod (p^2))^2 = 0 := by
      rw [← Nat.cast_pow,ZMod.natCast_self]
    rw [hz,zero_mul]
  change ρ (value a t) = ρ (a 0) + ρ (a 1) * ρ t
  rw [splitValue a ht,map_add,map_add,map_mul,map_mul,map_pow,zeroSq,zero_mul,add_zero]

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem existsUniqueNegativeSix : ∃! t : ℤ_[7], 8^6*(1+t)=1 := by
  have hunit : IsUnit (8 : ℤ_[7]) := by
    by_contra hu
    have hn := PadicInt.not_isUnit_iff.mp hu
    have hd : (7:ℤ) ∣ 8 := (PadicInt.norm_int_lt_one_iff_dvd (p:=7) 8).mp (by simpa using hn)
    norm_num at hd
  obtain ⟨u,hu⟩ := hunit.pow 6
  refine ⟨(↑u⁻¹:ℤ_[7])-1,?_,?_⟩
  · rw [← hu]; simp
  · intro t ht
    calc
      t = (↑u⁻¹:ℤ_[7]) * (8^6*(1+t))-1 := by rw [← hu,← mul_assoc]; simp
      _ = _ := by rw [ht,mul_one]

/-- The negative interpolation coordinate is characterized by 8^6 (1+t)=1.
Every integral 7-adic power series with the two stated residues has the same normalized slope. -/
theorem negativeSixSample (a : ℕ → ℤ_[7]) (t : ℤ_[7])
    (coord : 8^6*(1+t)=1) (h0 : PadicInt.toZModPow 2 (a 0)=24)
    (hs : PadicInt.toZModPow 2 (value a t)=3) :
    (7 * PadicInt.toZModPow 2 (a 1) : ZMod 49) = 28 ∧
    (7 * PadicInt.toZModPow 2 (a 1) : ZMod 49) * 47 = 42 := by
  have ht : (7:ℤ_[7]) ∣ t := by
    refine ⟨(-37449)*(1+t), ?_⟩
    linear_combination coord
  let ρ := (PadicInt.toZModPow 2 : ℤ_[7] →+* ZMod 49)
  have hc : (8:ZMod 49)^6*(1+ρ t)=1 := by
    have hj := congrArg ρ coord
    have h8 : ρ (8:ℤ_[7]) = 8 := map_ofNat ρ 8
    simpa only [map_mul,map_pow,map_add,map_one,h8] using hj
  have arg : ρ t = 7*(-6:ZMod 49) := by
    have inverse : (8:ZMod 49)^6 * 8=1 := by decide
    calc
      ρ t = 8*((8:ZMod 49)^6*(1+ρ t))-1 := by
        linear_combination -(1 + ρ t) * inverse
      _ = _ := by rw [hc]; decide
  have hc0 : ρ (a 0)=24 := h0
  have hs' : (3:ZMod 49) = ρ (a 0) + ρ (a 1)*ρ t := hs.symm.trans (reduceValue a ht)
  rw [hc0,arg] at hs'
  have first : (3:ZMod 49) = 24+(-6)*(7*ρ (a 1)) := by rw [hs']; ring
  apply BD.Examples.derivativeNormalization _ _ first
  have hunit : (24:ZMod 49)*47=1 := by decide
  change 7 * ρ (a 1) = 24 * (7 * ρ (a 1) * 47)
  linear_combination -(7*ρ (a 1))*hunit

end BD.PadicJet

