import BD.Arithmetic
import Mathlib.Data.Rat.Defs

set_option maxRecDepth 24000
set_option maxHeartbeats 6000000

/-! Evaluation of the exponential generating series for generalized Bernoulli numbers.
The defining recursion uses exact rationals. All indices used by the paper are small. -/
namespace BD.Arithmetic

/-- Multiplicative recursion for the binomial coefficient. -/
def chooseSmall (n k : Nat) : Nat :=
  (List.range k).foldl (fun c j => c * (n-j) / (j+1)) 1

/-- Entry n of the new array is B_(n,delta). Expanding
(e^(ft)-1) sum B_k t^k/k! = t sum delta(a) e^(at) gives the recursion. -/
def bernoulliUpTo : Nat → List Rat
  | 0 => []
  | n+1 =>
    let vals := bernoulliUpTo n
    let carry := (List.range n).foldl (fun total k =>
      total + (chooseSmall (n+1) k : Rat) * (687 : Rat)^(n+1-k) * vals.getD k 0) 0
    let top := (n+1 : Rat) * (powerSum n : Rat) - carry
    vals ++ [top / ((n+1 : Rat)*687)]

def specialValue (n : Nat) : Rat := -((bernoulliUpTo (n+2)).getD (n+1) 0) / (n+1 : Rat)

theorem bernoulliCrosscheckZero : specialValue 0 = 12 := by decide +kernel
theorem bernoulliCrosscheckSix : specialValue 6 = -10344805682225424 := by decide +kernel

theorem exactMinusTwelve :
    specialValue 12 = 11669195118821150724043145141695584 := by decide +kernel

theorem exactMinusFortyTwo : specialValue 42 =
    -498465604963330934325492313169818008187227792911781108007151910214379925549782983927876656259460376720284722479781354316986863813726580464 := by
  decide +kernel

/-- A rational residue is asserted by clearing the reduced denominator, explicitly a unit. -/
def secant (n : Nat) : Rat := (((1 + (7:Rat)^n) * specialValue n) - 24) / (-(n:Rat)*24)

def slopeResidue (n : Nat) : Bool :=
  let q := secant n
  (q.den % 7 != 0) && ((q.num - 42*(q.den:Int)) % 49 == 0)

/-- Exact rational secants before reduction. All three denominators are prime to seven. -/
theorem exactSecants :
    secant 6 = 16903699840469737967 / 2 ∧
    secant 12 = -2243287236885834206161269702021938380543277 / 4 ∧
    secant 42 =
      308547719403732974500506967411170520933012257182789390877683367390331843173849073762049259507771306277990914367625944122387793641775061655056327598908065597111824075011681 / 2 := by
  unfold secant
  rw [bernoulliCrosscheckSix,exactMinusTwelve,exactMinusFortyTwo]
  decide +kernel

theorem secantSix : slopeResidue 6 = true := by
  unfold slopeResidue
  rw [exactSecants.1]
  decide +kernel

theorem secantTwelve : slopeResidue 12 = true := by
  unfold slopeResidue
  rw [exactSecants.2.1]
  decide +kernel

theorem secantFortyTwo : slopeResidue 42 = true := by
  unfold slopeResidue
  rw [exactSecants.2.2]
  decide +kernel

end BD.Arithmetic

