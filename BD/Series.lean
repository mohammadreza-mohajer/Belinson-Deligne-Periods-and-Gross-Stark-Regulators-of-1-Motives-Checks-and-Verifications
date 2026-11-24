import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.Ring

/-! Leading terms of actual formal Taylor series. Factoring off X^r records
a lower bound even when the expected coefficient is zero. -/
namespace BD.Series
open PowerSeries
variable {K : Type*} [Field K]

/-- The Taylor coefficient of the indicated order; no nonvanishing is required. -/
def HasTerm (F : PowerSeries K) (r : ℕ) (a : K) : Prop :=
  ∃ u : PowerSeries K, F = X^r * u ∧ constantCoeff K u = a

theorem term_coeff {F : PowerSeries K} {r : ℕ} {a : K} (h : HasTerm F r a) :
    coeff K r F = a ∧ ∀ j < r, coeff K j F = 0 := by
  obtain ⟨u,rfl,hu⟩ := h
  constructor
  · simpa [coeff_zero_eq_constantCoeff_apply] using (coeff_X_pow_mul u r 0).trans
      (by simpa [coeff_zero_eq_constantCoeff_apply] using hu)
  · intro j hj
    rw [coeff_X_pow_mul', if_neg (Nat.not_le_of_lt hj)]

theorem exactOrder {F : PowerSeries K} {r : ℕ} {a : K} (h : HasTerm F r a) :
    F.order = r ↔ a ≠ 0 := by
  obtain ⟨hc,hv⟩ := term_coeff h
  rw [order_eq_nat, hc]
  exact and_iff_left hv

theorem product {F G : PowerSeries K} {r s : ℕ} {a b : K}
    (hf : HasTerm F r a) (hg : HasTerm G s b) : HasTerm (F*G) (r+s) (a*b) := by
  obtain ⟨u,rfl,hu⟩ := hf
  obtain ⟨v,rfl,hv⟩ := hg
  refine ⟨u*v,?_,?_⟩
  · rw [pow_add]; ac_rfl
  · rw [map_mul,hu,hv]

theorem power {F : PowerSeries K} {r : ℕ} {a : K} (h : HasTerm F r a) (n : ℕ) :
    HasTerm (F^n) (r*n) (a^n) := by
  induction n with
  | zero => exact ⟨1,by simp,by simp⟩
  | succ n ih => simpa [pow_succ,Nat.mul_succ] using product ih h

theorem finiteProduct {I : Type*} (s : Finset I) (F : I → PowerSeries K)
    (r : I → ℕ) (a : I → K) (h : ∀ i ∈ s, HasTerm (F i) (r i) (a i)) :
    HasTerm (∏ i ∈ s, F i) (∑ i ∈ s, r i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by simp,by simp⟩
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [hi] using product h₁ h₂

/-- Cancellation of t split poles, written without division by a nonunit power of X. -/
theorem splitCancellation (F U : PowerSeries K) {r t : ℕ} (ht : t ≤ r)
    (hs : X^t * F = X^r * U) : HasTerm F (r-t) (constantCoeff K U) := by
  refine ⟨U,?_,rfl⟩
  have h : X^t * F = X^t * (X^(r-t)*U) := calc
    X^t * F = X^r * U := hs
    _ = X^t * (X^(r-t)*U) := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
  ext j
  simpa only [coeff_X_pow_mul] using congrArg (coeff K (j+t)) h

/-- The factor of (minus one half)^b at the complex place is accounted for explicitly. -/
theorem complexLeading (L Z : PowerSeries K) (b : ℕ) (a z : K)
    (hL : HasTerm L 0 a) (hZ : HasTerm Z 0 z) {F : PowerSeries K} {r : ℕ} {c : K}
    (hf : HasTerm F r c) : HasTerm (Z^b * L * F) r (z^b*a*c) := by
  simpa using product (product (power hZ b) hL) hf

theorem ellipticExceptional {F E : PowerSeries K} {r : ℕ} {a e : K}
    (hf : HasTerm F r a) (he : HasTerm E 1 e) (ha : a ≠ 0) (hn : e ≠ 0) :
    (F*E).order = (r+1 : ℕ) ∧ coeff K (r+1) (F*E) = a*e := by
  have h := product hf he
  exact ⟨(exactOrder h).mpr (mul_ne_zero ha hn),(term_coeff h).1⟩

end BD.Series

