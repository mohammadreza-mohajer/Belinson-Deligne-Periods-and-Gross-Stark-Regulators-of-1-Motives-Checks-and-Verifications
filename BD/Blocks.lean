import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Simultaneous blocks may have different dimensions, multiplicities zero, or
zero-dimensional spaces. -/
namespace BD.Blocks
open Matrix
open scoped BigOperators
variable {J K : Type*} [Fintype J] [LinearOrder J] [CommRing K]
variable {N : J → Type*} [∀ j,Fintype (N j)] [∀ j,DecidableEq (N j)]

theorem determinantSum (M : ∀ j, Matrix (N j) (N j) K) :
    (blockDiagonal' M).det = ∏ j, (M j).det := by
  let tag : Sigma N → J := Sigma.fst
  have tri : (blockDiagonal' M).BlockTriangular tag := by
    rintro ⟨j,a⟩ ⟨k,b⟩ h
    exact blockDiagonal'_apply_ne M a b (ne_of_gt h)
  rw [tri.det_fintype]
  apply Finset.prod_congr rfl
  intro j _
  let e : N j ≃ {x : Sigma N // tag x = j} := {
    toFun := fun a => ⟨⟨j,a⟩,rfl⟩
    invFun := fun x => (show x.val.1=j from x.property) ▸ x.val.2
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨_,a⟩,rfl⟩; rfl }
  rw [← det_submatrix_equiv_self e ((blockDiagonal' M).toSquareBlock tag j)]
  congr 1
  apply Matrix.ext
  intro a b
  exact blockDiagonal'_apply_eq M j a b

/-- The full product of normalized block determinants in Theorem 6.4. -/
theorem repeatedDeterminant (m : J → ℕ) (M : ∀ j, Matrix (N j) (N j) K) :
    (blockDiagonal' (fun j => blockDiagonal (fun _ : Fin (m j) => M j))).det =
      ∏ j, (M j).det ^ m j := by
  rw [determinantSum]
  simp [det_blockDiagonal]

omit [∀ j,DecidableEq (N j)] in
theorem repeatedTrace (m : J → ℕ) (M : ∀ j, Matrix (N j) (N j) K) :
    (blockDiagonal' (fun j => blockDiagonal (fun _ : Fin (m j) => M j))).trace =
      ∑ j, m j • (M j).trace := by
  classical
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sigma, Fintype.sum_prod_type,
    blockDiagonal'_apply_eq, blockDiagonal_apply, Finset.sum_nsmul, Finset.mul_sum]

theorem characteristicSum (M : ∀ j, Matrix (N j) (N j) K) :
    (blockDiagonal' M).charpoly = ∏ j, (M j).charpoly := by
  have h : (blockDiagonal' M).charmatrix = blockDiagonal' (fun j => (M j).charmatrix) := by
    apply Matrix.ext
    rintro ⟨j,a⟩ ⟨k,b⟩
    by_cases he : j=k
    · subst k
      by_cases hab : a=b
      · subst b; simp [charmatrix_apply_eq,blockDiagonal'_apply_eq]
      · have hs : (Sigma.mk j a : Sigma N) ≠ ⟨j,b⟩ := by simpa using hab
        simp [charmatrix_apply_ne _ _ _ hs,blockDiagonal'_apply_eq,charmatrix_apply_ne _ _ _ hab]
    · have hs : (Sigma.mk j a : Sigma N) ≠ ⟨k,b⟩ := fun h => he (congrArg Sigma.fst h)
      simp [charmatrix_apply_ne _ _ _ hs,blockDiagonal'_apply_ne _ _ _ he]
  simp only [charpoly,h,determinantSum]

theorem singleSizeCharpoly {T W : Type*} [Fintype T] [DecidableEq T]
    [Fintype W] [DecidableEq W] (A : T → Matrix W W K) :
    (blockDiagonal A).charpoly = ∏ t, (A t).charpoly := by
  have h : (blockDiagonal A).charmatrix = blockDiagonal (fun t => (A t).charmatrix) := by
    apply Matrix.ext
    rintro ⟨a,t⟩ ⟨b,u⟩
    by_cases htu : t=u
    · subst u
      by_cases hab : a=b
      · subst b; simp [charmatrix_apply_eq]
      · have hpair : (a,t) ≠ (b,t) := fun he => hab (congrArg Prod.fst he)
        simp [charmatrix_apply_ne _ _ _ hpair, charmatrix_apply_ne _ _ _ hab]
    · have hpair : (a,t) ≠ (b,u) := fun he => htu (congrArg Prod.snd he)
      simp [charmatrix_apply_ne _ _ _ hpair,blockDiagonal_apply_ne _ _ _ htu]
  simp only [charpoly,h,det_blockDiagonal]

theorem repeatedCharpoly (m : J → ℕ) (M : ∀ j, Matrix (N j) (N j) K) :
    (blockDiagonal' (fun j => blockDiagonal (fun _ : Fin (m j) => M j))).charpoly =
      ∏ j, (M j).charpoly^m j := by
  rw [characteristicSum]
  simp [singleSizeCharpoly]

end BD.Blocks

