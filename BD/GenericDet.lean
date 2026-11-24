import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Polynomial left inverse for the determinants of disjoint generic blocks of
arbitrary positive and possibly different sizes, used in Theorem 6.8. -/
namespace BD.GenericDet
open Matrix MvPolynomial
variable {J K : Type*} [CommRing K]
abbrev Entry (d : J → ℕ) := (j : J) × (Fin (d j+1) × Fin (d j+1))

noncomputable def block (d : J → ℕ) (j : J) :
    Matrix (Fin (d j+1)) (Fin (d j+1)) (MvPolynomial (Entry d) K) :=
  Matrix.of fun i k => X ⟨j,i,k⟩

noncomputable def detMap (d : J → ℕ) : MvPolynomial J K →ₐ[K] MvPolynomial (Entry d) K :=
  aeval (fun j => (block (K:=K) d j).det)

noncomputable def specialize (d : J → ℕ) :
    MvPolynomial (Entry d) K →ₐ[K] MvPolynomial J K :=
  aeval (fun a => if a.2.1 = a.2.2 then
    (if a.2.1 = 0 then X a.1 else 1) else 0)

theorem specializeBlock (d : J → ℕ) (j : J) :
    specialize d ((block (K:=K) d j).det) = X j := by
  classical
  rw [AlgHom.map_det]
  have hd : (specialize (K:=K) d).mapMatrix (block d j) =
      Matrix.diagonal (fun i : Fin (d j+1) => if i=0 then (X j : MvPolynomial J K) else 1) := by
    apply Matrix.ext
    intro i k
    change specialize (K:=K) d (X ⟨j,(i,k)⟩) = _
    simp [specialize,Matrix.diagonal_apply]
  rw [hd,Matrix.det_diagonal]
  simp

theorem leftInverse (d : J → ℕ) :
    (specialize (K:=K) d).comp (detMap d) = AlgHom.id K (MvPolynomial J K) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [detMap,specializeBlock]

theorem independentDeterminants (d : J → ℕ) : Function.Injective (detMap (K:=K) d) := by
  intro f g he
  have hh := congrArg (specialize (K:=K) d) he
  have hf (x : MvPolynomial J K) : specialize d (detMap d x) = x :=
    DFunLike.congr_fun (leftInverse (K:=K) d) x
  simpa only [hf] using hh

end BD.GenericDet

