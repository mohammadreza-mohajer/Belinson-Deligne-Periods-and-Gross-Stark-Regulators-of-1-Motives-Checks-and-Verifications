import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Determinant identities of the inertia sequence for arbitrary block sizes.
The input bases here correspond to the exact sequences (2.2) and (2.3). -/
namespace BD.Euler
open Matrix
open scoped BigOperators
variable {K m n : Type*} [CommRing K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]

def factor (A : Matrix n n K) (t : K) : K := (1-t • A).det

theorem blockFactor (A : Matrix m m K) (B : Matrix m n K) (D : Matrix n n K) (t : K) :
    factor (fromBlocks A B 0 D) t = factor A t * factor D t := by
  have h : (1-t • fromBlocks A B 0 D) =
      fromBlocks (1-t • A) (-(t • B)) 0 (1-t • D) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.fromBlocks]
  simp only [factor,h,det_fromBlocks_zero₂₁]

theorem constantFactor (t : K) :
    factor (1 : Matrix n n K) t = (1-t)^Fintype.card n := by
  have h : (1-t • (1 : Matrix n n K)) = diagonal (fun _ : n => 1-t) := by
    ext i j
    by_cases hh : i=j <;> simp [Matrix.one_apply,diagonal_apply,hh]
  simp [factor,h,det_diagonal]

/-- Division-free Euler correction, valid even where the discarded factor vanishes. -/
theorem correction {K₀ G Y M D : K} (mixed : M=G*K₀) (graded : Y=K₀*D) :
    M*D=G*Y := by rw [mixed,graded,mul_assoc]

theorem inertSignFactor (t : K) :
    factor (diagonal (fun _ : Unit => (-1:K))) t = 1+t := by
  simp [factor,Matrix.det_unique]

end BD.Euler

