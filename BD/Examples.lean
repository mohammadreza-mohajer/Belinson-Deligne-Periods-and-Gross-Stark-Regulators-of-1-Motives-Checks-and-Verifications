import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Character arithmetic and first-order interpolation in Z/49. -/
namespace BD.Examples
open scoped BigOperators

inductive Class where | id | swap | cycle deriving DecidableEq, Repr

def trivial : Class → ℤ := fun _ => 1
def sign : Class → ℤ | .id => 1 | .swap => -1 | .cycle => 1
def standard : Class → ℤ | .id => 2 | .swap => 0 | .cycle => -1
def permThree : Class → ℤ | .id => 3 | .swap => 1 | .cycle => 0
def regular : Class → ℤ | .id => 6 | _ => 0

theorem characterRelation (c : Class) :
    regular c + trivial c = 2*permThree c + sign c := by cases c <;> decide

theorem decompositions (c : Class) :
    permThree c = trivial c + standard c ∧
    regular c = trivial c + sign c + 2*standard c := by cases c <;> decide

def fixedDim (χ : Class → ℤ) : ℤ := (χ .id + χ .swap)/2

theorem localDimensions : [fixedDim trivial, fixedDim sign, fixedDim standard,
    fixedDim permThree, fixedDim regular] = [1,0,1,2,3] := by decide

theorem coefficientIdentity {K : Type*} [CommRing K] (a b : K) :
    (a*b^2)*a = (a*b)^2 := by ring

theorem unscaledIdentity {K : Type*} [CommRing K] (a b : K) :
    (2^3*(a*b^2))*a = 2*(2*(a*b))^2 := by ring

theorem quotientIdentity {K : Type*} [Field K] {l a c d : K}
    (h : l*a=c^2*d) (hc : c≠0) : l*a/c^2=d := by
  rw [h, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hc)]

theorem towerOrder (m : ℕ) :
    (∑ _i : Fin (2^m), (1+2 : ℕ)) = 3*2^m := by simp [Nat.mul_comm]

/-- First-order Taylor expansion at any integer multiple of 7, for a polynomial of
arbitrary degree given by its coefficient list in ascending order. -/
def horner {R : Type*} [CommRing R] (z : R) : List R → R
  | [] => 0
  | a::v => a+z*horner z v

theorem squareZeroExpansion {R : Type*} [CommRing R] (z a b : R) (rest : List R)
    (hz : z^2=0) : horner z (a::b::rest) = a+z*b := by
  simp only [horner]
  calc
    _ = a+z*b+z^2*horner z rest := by ring
    _ = _ := by rw [hz,zero_mul,add_zero]

theorem sevenSquare (s : ZMod 49) : (7*s)^2=0 := by
  rw [mul_pow, show (7:ZMod 49)^2=0 by decide, zero_mul]

theorem sevenTangent (a b s : ZMod 49) (tail : List (ZMod 49)) :
    horner (7*s) (a::b::tail) = a+s*(7*b) := by
  rw [squareZeroExpansion _ _ _ _ (sevenSquare s)]
  ring

theorem eightPow (n : ℕ) : (8:ZMod 49)^n = 1+7*(n:ZMod 49) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,Nat.cast_succ]
    have h : (49:ZMod 49)=0 := by decide
    calc
      _ = (1+7*((n:ZMod 49)+1)) + 49*n := by ring
      _ = _ := by rw [h,zero_mul,add_zero]

theorem derivativeNormalization (d e : ZMod 49) (hs : 3=24+(-6)*d)
    (he : d=24*e) : d=28 ∧ e=42 := by
  have hu : (8:ZMod 49)*(-6) = 1 := by decide
  have hv : (47:ZMod 49)*24 = 1 := by decide
  have hd : d = 8 * (3-24 : ZMod 49) := by
    calc
      d = (8*(-6))*d := by rw [hu,one_mul]
      _ = 8*((24+(-6)*d)-24) := by ring
      _ = _ := by rw [← hs]
  have hd' : d=28 := hd.trans (by decide)
  refine ⟨hd',?_⟩
  calc
    e = (47*24)*e := by rw [hv,one_mul]
    _ = 47*d := by rw [he,mul_assoc]
    _ = 42 := by rw [hd']; decide

end BD.Examples

