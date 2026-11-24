import Std

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-! Exact arithmetic for Sections 4 and 8. All closed theorems use kernel reduction. -/
namespace BD.Arithmetic

/-- Quadratic sign at an odd prime, using Euler's criterion on units. -/
def signAt (p a : Nat) : Int :=
  if a % p = 0 then 0 else if ((a % p) ^ ((p-1)/2)) % p = 1 then 1 else -1

def delta (a : Nat) : Int := signAt 3 a * signAt 229 a

def powerSum (j : Nat) : Int :=
  (List.range 687).foldl (fun acc i => acc + delta (i+1) * (Int.ofNat (i+1)) ^ j) 0

def bernoulliSevenNumerator : Int :=
  let f : Int := 687
  6 * powerSum 7 - 21*f*powerSum 6 + 21*f^2*powerSum 5 - 7*f^4*powerSum 3 + f^6*powerSum 1

theorem characterMass : powerSum 0 = 0 := by decide
theorem sumOne : powerSum 1 = -8244 := by decide
theorem valueZero : -powerSum 1 = 687 * 12 := by decide
theorem valueMinusSix : -bernoulliSevenNumerator = (42*687) * (-10344805682225424) := by decide
theorem deltaAtSeven : delta 7 = -1 := by decide
theorem interpolatedResidues :
    2*(12 : Int) = 24 ∧ ((1 + 7^6)*(-10344805682225424 : Int)) % 49 = 3 := by decide

/-- Solving for the unnormalized and normalized derivatives modulo 49. -/
theorem uniqueSlopes :
    (List.range 49).filter (fun (n : Nat) => (24 + (-6:Int)*(n:Int)) % 49 == 3) = [28] ∧
    (List.range 49).filter (fun n => 24*n % 49 == 28) = [42] := by decide

def cubic (a : Int) : Int := a^3 - 4*a + 1

def roots (p : Nat) (f : Int → Int) : List Nat :=
  (List.range p).filter (fun n => f (n:Int) % (p:Int) == 0)

theorem cubicDiscriminant : -4*(-4:Int)^3 - 27*1^2 = 229 := by decide
theorem cubicRootTest : cubic 1 = -2 ∧ cubic (-1) = 4 := by decide
theorem discrBetweenSquares : 15^2 < 229 ∧ 229 < 16^2 := by decide
theorem quadraticNorms : (4:Int)^2 - 5 = 11 ∧ (5:Int)^2 + 3 = 4*7 := by decide
theorem splitAtEleven : roots 11 (fun x => x^2-5) = [4,7] := by decide
theorem cubicFactorsSeven :
    ((List.range 7).all fun n => (cubic n - ((n:Int)-4)*((n:Int)^2+4*n+5)) % 7 == 0) = true ∧
    roots 7 cubic = [4] ∧ roots 7 (fun x => x^2+4*x+5) = [] := by decide
theorem cubicRootsTwentyNine : roots 29 cubic = [13] := by decide
theorem quadraticLocalData :
    roots 7 (fun x => x^2+3) = [2,5] ∧ roots 29 (fun x => x^2+1) = [12,17] ∧
    roots 29 (fun x => x^2-229) = [] ∧ roots 29 (fun x => x^2+x+1) = [] := by decide
theorem discriminantData : (-3 : Int)*229 = -687 ∧ (-687:Int)%4=1 := by decide

/-- The nonzero square classes give a second, definitional calculation of each sign. -/
def squareSign (p a : Nat) : Int :=
  if a % p = 0 then 0 else
  if (List.range p).any (fun x => x*x % p == a%p) then 1 else -1

theorem signTableThree : (List.range 3).all (fun a => signAt 3 a == squareSign 3 a) = true := by decide
theorem signTable229 : (List.range 229).all (fun a => signAt 229 a == squareSign 229 a) = true := by decide

end BD.Arithmetic

