import BD.Arithmetic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum

/-! Connection of the executable sign table with mathlib's Legendre symbol. -/
namespace BD.Arithmetic

theorem signAt_eq_legendre (p a : ℕ) [Fact p.Prime] [Fact (2<p)] (hp : p%2=1) :
    signAt p a = legendreSym p (a:ℤ) := by
  haveI : Fact (1<p) := ⟨by have := (inferInstance : Fact (2<p)).out; omega⟩
  have he : (p-1)/2=p/2 := by omega
  have hz : (a:ZMod p)=0 ↔ a%p=0 := (ZMod.natCast_zmod_eq_zero_iff_dvd a p).trans Nat.dvd_iff_mod_eq_zero
  have hpow : ((a%p)^((p-1)/2))%p=1 ↔ (a:ZMod p)^(p/2)=1 := by
    rw [he, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_mod]
    rw [← ZMod.val_one p, (ZMod.val_injective p).eq_iff]
  have hpval := legendreSym.eq_pow p (a:ℤ)
  push_cast at hpval
  by_cases ha : a%p=0
  · have hzero := (legendreSym.eq_zero_iff p (a:ℤ)).mpr (by exact_mod_cast hz.mpr ha)
    simp [signAt,ha,hzero]
  · have hne : ((a:ℤ):ZMod p) ≠ 0 := by exact_mod_cast (fun h => ha (hz.mp h) : (a:ZMod p) ≠ 0)
    rcases legendreSym.eq_one_or_neg_one p hne with h | h
    · rw [h] at hpval ⊢
      have htest := hpow.mpr (by simpa using hpval.symm)
      simp [signAt,ha,htest]
    · rw [h] at hpval ⊢
      have htest : ¬(((a%p)^((p-1)/2))%p=1) := by
        intro ho
        have heq : (-1:ZMod p)=1 := by simpa using hpval.trans (hpow.mp ho)
        exact ZMod.neg_one_ne_one heq
      simp [signAt,ha,htest]

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
set_option maxRecDepth 10000 in
instance : Fact (Nat.Prime 229) := ⟨by decide +kernel⟩

theorem delta_legendre (a : ℕ) :
    delta a = legendreSym 3 (a:ℤ) * legendreSym 229 (a:ℤ) := by
  letI : Fact (2<3) := ⟨by decide⟩
  letI : Fact (2<229) := ⟨by decide⟩
  simp only [delta,signAt_eq_legendre 3 a (by decide),signAt_eq_legendre 229 a (by decide)]

end BD.Arithmetic

