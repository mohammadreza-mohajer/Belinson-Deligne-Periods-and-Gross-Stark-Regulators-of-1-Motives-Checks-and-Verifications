import BD.Examples
import Mathlib.Tactic.DeriveFintype

namespace BD.Permutations
open BD.Examples
inductive Letter where | a | b | c deriving DecidableEq, Fintype
inductive Perm where | id | ab | ac | bc | abc | acb deriving DecidableEq, Fintype

def images : Perm → Letter × Letter × Letter
  | .id => (.a,.b,.c) | .ab => (.b,.a,.c) | .ac => (.c,.b,.a)
  | .bc => (.a,.c,.b) | .abc => (.b,.c,.a) | .acb => (.c,.a,.b)

def act (g : Perm) : Letter → Letter
  | .a => (images g).1 | .b => (images g).2.1 | .c => (images g).2.2

def cls : Perm → Class
  | .id => .id | .abc | .acb => .cycle | _ => .swap

theorem permutationsInjective : ∀ g : Perm, Function.Injective (act g) := by decide +kernel

theorem enumerationComplete (f : Letter → Letter) (hf : Function.Injective f) :
    ∃ g : Perm, act g=f := by
  have complete : ∀ x y z : Letter, x≠y → x≠z → y≠z →
      ∃ g : Perm, act g .a=x ∧ act g .b=y ∧ act g .c=z := by decide +kernel
  obtain ⟨g,ha,hb,hc⟩ := complete (f .a) (f .b) (f .c)
    (fun h => (by decide : Letter.a ≠ .b) (hf h))
    (fun h => (by decide : Letter.a ≠ .c) (hf h))
    (fun h => (by decide : Letter.b ≠ .c) (hf h))
  exact ⟨g,funext fun x => by cases x <;> assumption⟩

theorem enumerationUnique : Function.Injective images := by decide +kernel

def fixedLetters (g : Perm) : ℕ :=
  ([Letter.a,.b,.c].filter fun i => act g i == i).length

def inversions (g : Perm) : ℕ :=
  let index : Letter → ℕ := fun | .a => 0 | .b => 1 | .c => 2
  ([(Letter.a,Letter.b),(.a,.c),(.b,.c)].filter fun (i,j) => index (act g i) > index (act g j)).length

theorem charactersOfAction : ∀ g : Perm,
    (fixedLetters g : ℤ) = permThree (cls g) ∧ (-1:ℤ)^(inversions g) = sign (cls g) := by decide +kernel

theorem orderSixInduction {K : Type*} [Field K] (ω : K) (h : ω^2+ω+1=0) :
    ω + ω^2 = -1 := by rw [add_comm]; exact eq_neg_of_add_eq_zero_left h

end BD.Permutations

