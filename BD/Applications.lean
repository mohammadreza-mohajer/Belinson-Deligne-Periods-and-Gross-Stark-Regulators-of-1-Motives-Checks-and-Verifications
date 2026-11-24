import BD.Matrices
import BD.Series
import BD.Characters
import BD.Linear
import Mathlib.Tactic.Ring

/-! Formal consequences combining analytic Taylor inputs with linear algebra. -/
namespace BD.Applications
open Matrix PowerSeries
open scoped Matrix BigOperators

theorem grossExactIffNoPureLift {I K : Type*} [Field K] [Fintype I] [DecidableEq I]
    (B : Matrix I I K) (F : PowerSeries K) (r : ℕ) (c : K) (hc : c≠0)
    (h : BD.Series.HasTerm F r (c*B.det)) :
    F.order = r ↔ (∀ y : I → K, B.transpose *ᵥ y = 0 → y=0) := by
  have nz : c*B.det ≠ 0 ↔ B.det ≠ 0 :=
    ⟨fun hn hzero => hn (by rw [hzero,mul_zero]),mul_ne_zero hc⟩
  rw [BD.Series.exactOrder h,nz]
  constructor
  · intro hd y hy
    exact Matrix.eq_zero_of_mulVec_eq_zero (by simpa using hd : B.transpose.det≠0) hy
  · intro hn hd
    have hdt : B.transpose.det=0 := by simpa using hd
    obtain ⟨y,hne,hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdt
    exact hne (hn y hy)

/-- The normalization has a precise meaning even if the expected coefficient vanishes. -/
theorem grossCoefficient {I K : Type*} [Field K] [Fintype I] [DecidableEq I]
    (B : Matrix I I K) (F : PowerSeries K) (r : ℕ) (c : K) (hc : c≠0)
    (h : BD.Series.HasTerm F r (c*B.det)) : coeff K r F / c = B.det := by
  rw [(BD.Series.term_coeff h).1,mul_comm,mul_div_cancel_right₀ _ hc]

theorem ordinaryUnitRoot {K : Type*} [Field K] (u a p : K)
    (hu : u^2-a*u+p=0) (hcard : p+1-a≠0) : u≠1 := by
  rintro rfl
  apply hcard
  simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hu

theorem ordinaryProduct {K : Type*} [Field K] {F E : PowerSeries K} {a e : K} {r : ℕ}
    (hf : BD.Series.HasTerm F r a) (he : BD.Series.HasTerm E 0 e) (ha : a≠0) (hb : e≠0) :
    (F*E).order=r ∧ coeff K r (F*E)=a*e := by
  have h : BD.Series.HasTerm (F*E) r (a*e) := by simpa using BD.Series.product hf he
  exact ⟨(BD.Series.exactOrder h).mpr (mul_ne_zero ha hb),(BD.Series.term_coeff h).1⟩

end BD.Applications

