import BD.Interpolation
import BD.Separation
import BD.Tails
import BD.Relations
import Mathlib.Algebra.Polynomial.BigOperators

/-! Final isolation step for a maximal conductor scale in the proof of Theorem 7.1.
The tail hypotheses are where arithmetic interpolation, scale selection and Chebotarev enter. -/
namespace BD.Artin
open Filter Topology Polynomial
open scoped BigOperators
variable {K I C : Type*} [NormedField K] [Fintype I]

/-- All polynomial coefficients at a fixed leading scale vanish once each monomial
in Frobenius traces has isolating samples with a vanishing normalized remainder. -/
theorem isolateScale (x : I → C → K) (hx : Function.Injective x)
    (w : I → K) (hw : ∀ i,w i≠0) (P : I → K[X])
    (samples : ∀ d : C →₀ ℕ, ∃ z tail : ℕ → K,
      (∀ᶠ n in atTop, z n≠0) ∧ Tendsto (fun n => (z n)⁻¹) atTop (𝓝 0) ∧
      Tendsto tail atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, (∑ i, (w i*d.prod (fun c e => x i c^e))*(P i).eval (z n))+tail n=0) :
    ∀ i, P i = 0 := by
  classical
  have van (d : C →₀ ℕ) : (∑ i, Polynomial.C (w i*d.prod (fun c e => x i c^e))*P i) = 0 := by
    obtain ⟨z,t,hn,hi,ht,hh⟩ := samples d
    apply BD.Interpolation.leadingFrequency z t hn hi _ ht
    simpa only [eval_finset_sum, eval_mul,eval_C] using hh
  intro i
  apply Polynomial.ext
  intro n
  rw [coeff_zero]
  apply BD.Separation.weighted_moments x hx (fun j => (P j).coeff n) w hw _ i
  intro d
  have hh := congrArg (fun Q : K[X] => Q.coeff n) (van d)
  simp only [finset_sum_coeff, coeff_C_mul,coeff_zero] at hh
  simp only [mul_right_comm (w _) _ ((P _).coeff n)] at hh
  exact hh

end BD.Artin

