import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Local regulator matrices, including the full principal-minor expansion. -/
namespace BD.Matrices
open Matrix
open scoped BigOperators Matrix
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Evaluation row of the local cup pairing, in the ordered valuation/logarithm coordinates. -/
def obstruction (V L : Matrix n n R) (x y : n → R) : n → R :=
  x ᵥ* V + y ᵥ* L

theorem liftGraph (V W L B : Matrix n n R) (hVW : V*W=1) (hL : L=B*V)
    (x y : n → R) : obstruction V L x y = 0 ↔ x = -(B.transpose *ᵥ y) := by
  have hid : obstruction V L x y = (x + y ᵥ* B) ᵥ* V := by
    rw [obstruction, hL, add_vecMul, vecMul_vecMul]
  rw [hid, mulVec_transpose]
  constructor
  · intro h
    have hr := congrArg (fun z : n → R => z ᵥ* W) h
    simp only [vecMul_vecMul, hVW, vecMul_one, zero_vecMul] at hr
    exact eq_neg_of_add_eq_zero_left hr
  · intro h
    simp [h]

/-- A simultaneous change of logarithm branch translates the regulator. -/
theorem branchShift (L O W : Matrix n n R) (h : O*W=1) (c : R) :
    (L-c • O)*W = L*W-c • (1 : Matrix n n R) := by
  rw [sub_mul, smul_mul_assoc, h]

/-- With V = D O, the correctly ordered inverse is W Dinv. -/
theorem normalizeValuations (D Dinv O W L : Matrix n n R)
    (ho : W*O=1) (hd : Dinv*D=1) :
    (L*W*Dinv)*(D*O) = L := by
  calc
    _ = L * (W * ((Dinv * D) * O)) := by simp only [Matrix.mul_assoc]
    _ = L := by rw [hd, one_mul, ho, mul_one]

/-- Simultaneous comparison across a change of bases by S and its inverse W. -/
theorem descentConjugacy (S W B : Matrix n n R) (hw : W*S=1) :
    (S*B*W)*S=S*B := by rw [Matrix.mul_assoc, hw, mul_one]

theorem determinantConjugacy (S W B : Matrix n n R) (h : S*W=1) :
    (S*B*W).det=B.det := by
  have hd := congrArg Matrix.det h
  rw [det_mul, det_one] at hd
  rw [det_mul, det_mul, mul_right_comm, hd, one_mul]

/-- Principal submatrix on the indices of a finite set. -/
def minor (B : Matrix n n R) (s : Finset n) : R :=
  (B.submatrix (fun i : s => (i:n)) (fun i : s => (i:n))).det

private theorem mixedRows (A : Matrix n n R) (t : n → R) (s : Finset n) :
    Matrix.det (s.piecewise A (diagonal t)) =
      minor A s * ∏ i : {i // i ∉ s}, t i := by
  classical
  let e := Equiv.sumCompl (fun i : n => i ∈ s)
  let U : Matrix s s R := A.submatrix Subtype.val Subtype.val
  let V : Matrix s {i // i ∉ s} R := A.submatrix Subtype.val Subtype.val
  let D : Matrix {i // i ∉ s} {i // i ∉ s} R := diagonal (fun i => t i)
  let M : Matrix n n R := s.piecewise A (diagonal t)
  have blocks : M.submatrix e e = fromBlocks U V 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j <;> simp [e, M, U, V, Finset.piecewise, i.property, Matrix.submatrix]
    | inr i =>
      cases j with
      | inl j =>
        have hne : (i:n) ≠ (j:n) := fun he => i.property (he ▸ j.property)
        simp [e,M,Finset.piecewise,i.property,diagonal_apply,hne,Matrix.submatrix]
      | inr j =>
        by_cases hij : i=j
        · subst j
          simp [e,M,D,Finset.piecewise,i.property,Matrix.submatrix]
        · have hne : (i:n) ≠ (j:n) := fun hh => hij (Subtype.ext hh)
          simp [e,M,D,Finset.piecewise,i.property,diagonal_apply,hne,hij,Matrix.submatrix]
  change M.det = _
  rw [← det_submatrix_equiv_self e M, blocks, det_fromBlocks_zero₂₁, det_diagonal]
  rfl

/-- Multiaffine determinant identity, for every finite size including zero. -/
theorem principalMinorExpansion (t : n → R) (B : Matrix n n R) :
    (diagonal t - B).det =
      ∑ s : Finset n, (-1:R)^s.card * minor B s * ∏ i : {i // i ∉ s}, t i := by
  classical
  rw [sub_eq_add_neg, add_comm]
  change (detRowAlternating (R := R) (n := n)).toMultilinearMap (-B + diagonal t) = _
  rw [MultilinearMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  change Matrix.det (s.piecewise (-B) (diagonal t)) = _
  rw [mixedRows]
  have hneg : minor (-B) s = (-1:R)^s.card * minor B s := by
    change (-(B.submatrix (fun i:s => (i:n)) (fun i:s => (i:n)))).det = _
    simp [det_neg, minor]
  rw [hneg]

theorem existsLift_iff_det {K : Type*} [Field K] (B : Matrix n n K) (t : n → K) :
    (∃ y : n → K, y ≠ 0 ∧ (diagonal t - B.transpose) *ᵥ y = 0) ↔
      (diagonal t-B).det = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff]
  have h : diagonal t - B.transpose = (diagonal t-B).transpose := by simp
  rw [h, det_transpose]

end BD.Matrices

