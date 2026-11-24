import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! An absolutely convergent family of frequencies strictly below the leading scale.
A polynomial prefactor of any fixed degree is allowed. -/
namespace BD.Tails
open Filter Topology
open scoped BigOperators

theorem envelope {I : Type*} (w x : I → ℝ) (ρ : ℝ) (hw : Summable w)
    (hn : ∀ i, 0≤w i) (hx : ∀ i, 0≤x i) (hb : ∀ i,x i≤ρ) (n : ℕ) :
    (∑' i, w i * x i^n) ≤ (∑' i, w i)*ρ^n := by
  have hle (i : I) : w i*x i^n ≤ w i*ρ^n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hx i) (hb i) n) (hn i)
  have h₁ := hw.mul_right (ρ^n)
  have h₂ := Summable.of_nonneg_of_le (fun i => mul_nonneg (hn i) (pow_nonneg (hx i) _)) hle h₁
  simpa only [tsum_mul_right] using h₂.tsum_le_tsum hle h₁

theorem polynomialTail {I : Type*} (w x : I → ℝ) (ρ : ℝ) (hw : Summable w)
    (hn : ∀ i,0≤w i) (hx : ∀ i,0≤x i) (hb : ∀ i,x i≤ρ)
    (hρ : 0≤ρ) (h : ρ<1) (d : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^d * ∑' i, w i*x i^n) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (tsum_nonneg fun i => mul_nonneg (hn i) (pow_nonneg (hx i) _))
  · intro n
    exact mul_le_mul_of_nonneg_left (envelope w x ρ hw hn hx hb n) (pow_nonneg (Nat.cast_nonneg n) _)
  · have ht := (tendsto_pow_const_mul_const_pow_of_lt_one d hρ h).const_mul (∑' i, w i)
    simpa only [mul_zero, mul_left_comm, mul_assoc] using ht

end BD.Tails

