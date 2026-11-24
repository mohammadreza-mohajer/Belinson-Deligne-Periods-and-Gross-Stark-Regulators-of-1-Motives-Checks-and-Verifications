import BD.Series
import BD.Examples

/-! The first Taylor jet of an arbitrary formal Iwasawa series, with no bound on
the length of its coefficient list. It gives a well-defined square-zero evaluation. -/
namespace BD.Jet
open PowerSeries
variable {R : Type*} [CommRing R]

theorem firstCoeffMul (f g : PowerSeries R) :
    coeff R 1 (f*g) = constantCoeff R f * coeff R 1 g + coeff R 1 f * constantCoeff R g := by
  rw [coeff_mul]
  have ha : Finset.antidiagonal (1:ℕ) = {(0,1),(1,0)} := by decide
  rw [ha]
  simp [coeff_zero_eq_constantCoeff_apply, add_comm]

/-- Evaluation at a square-zero element factors through the first jet of R[[X]]. -/
noncomputable def firstJet (z : R) (hz : z^2=0) : PowerSeries R →+* R where
  toFun f := constantCoeff R f + z * coeff R 1 f
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp; ring
  map_mul' f g := by
    simp only [map_mul,firstCoeffMul]
    have h : (constantCoeff R f + z*coeff R 1 f)*(constantCoeff R g+z*coeff R 1 g) =
        constantCoeff R f*constantCoeff R g +
        z*(constantCoeff R f*coeff R 1 g + coeff R 1 f*constantCoeff R g) +
        z^2*(coeff R 1 f*coeff R 1 g) := by ring
    rw [h,hz,zero_mul,add_zero]

theorem integralIwasawaSlope (H : PowerSeries (ZMod 49)) (s : ZMod 49) :
    firstJet (7*s) (BD.Examples.sevenSquare s) H =
      constantCoeff _ H + s*(7*coeff _ 1 H) := by
  change _ + (7*s)*_ = _
  ring

theorem logTermValuation (n e : ℕ) (hn : 2≤n) (h : 7^e ∣ n) : e+2≤n := by
  have he := Nat.le_of_dvd (by omega : 0<n) h
  cases e with
  | zero => omega
  | succ j =>
    have bound (k : ℕ) : k+3≤7^(k+1) := by
      induction k with
      | zero => decide
      | succ k ih => rw [pow_succ]; omega
    have := bound j
    omega

/-- A single interpolation sample determines both residues for every integral series
in the coordinate T = 8^s-1 after reduction modulo 49. -/
theorem slopeFromSample (H : PowerSeries (ZMod 49)) (h0 : constantCoeff _ H = 24)
    (hs : firstJet (7*(-6:ZMod 49)) (BD.Examples.sevenSquare (-6)) H = 3) :
    7*coeff _ 1 H = 28 ∧ (7*coeff _ 1 H)*47 = 42 := by
  have hsample : (3:ZMod 49) = 24+(-6)*(7*coeff _ 1 H) := by
    rw [← h0, ← integralIwasawaSlope, hs]
  have hinv : (24:ZMod 49)*47=1 := by decide
  apply BD.Examples.derivativeNormalization _ _ hsample
  calc
    _ = (24*47)*(7*coeff _ 1 H) := by rw [hinv,one_mul]
    _ = _ := by ring

end BD.Jet

namespace BD.Jet
open PowerSeries

/-- Under a product identity a hidden factor with constant one changes the first
coefficient exactly when its own linear coefficient and the visible constant are nonzero. -/
theorem hiddenDerivative {K : Type*} [Field K] (L V H : PowerSeries K)
    (relation : L=V*H) (unitH : constantCoeff K H=1) :
    coeff K 1 L - coeff K 1 V = constantCoeff K V * coeff K 1 H := by
  rw [relation,firstCoeffMul,unitH,mul_one,add_sub_cancel_right]

theorem firstOrderFailure {K : Type*} [Field K] (L V H : PowerSeries K)
    (relation : L=V*H) (unitH : constantCoeff K H=1) (hV : constantCoeff K V≠0)
    (hH : coeff K 1 H≠0) : constantCoeff K L=constantCoeff K V ∧ coeff K 1 L≠coeff K 1 V := by
  constructor
  · rw [relation,map_mul,unitH,mul_one]
  · intro he
    have h := hiddenDerivative L V H relation unitH
    rw [he,sub_self] at h
    exact mul_ne_zero hV hH h.symm

end BD.Jet

