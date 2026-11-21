import Formalism.SharpRestriction.LevelLetterCocycles.DerivativeProdSubEval
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

theorem lemmaGD_cc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (hg : Good K 1 LL) :
    ∃ cc : ℤ → ↥(OL LL), ∀ x : ℤ, (-(((P.PD K).p : ℕ) : ↥(OL LL))) * cc x =
      ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) - 1 := by
  obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (H := H) hg
  have hne : (z : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  let I : Ideal ℤ_[l] := Ideal.span {((l : ℕ) : ℤ_[l])}
  have hI : (z : ℤ_[l]) - 1 ∈ I := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by omega)
    simpa using this
  have hz1 : Units.map (Ideal.Quotient.mk I).toMonoidHom z = 1 := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_one]
    exact (Ideal.Quotient.eq.2 hI).trans (map_one _)
  have hw : ∀ x : ℤ, ∃ w : ℤ_[l], -((l : ℕ) : ℤ_[l]) * w = ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    intro x
    have h1 : (Ideal.Quotient.mk I) ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) = (Ideal.Quotient.mk I) 1 := by
      have := congrArg Units.val
        (show Units.map (Ideal.Quotient.mk I).toMonoidHom (z ^ (-x)) = 1 by
          rw [map_zpow, hz1, one_zpow])
      rw [Units.coe_map, Units.val_one] at this
      exact this.trans (map_one _).symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    exact ⟨-w, by rw [← hw]; ring⟩
  choose w hw using hw
  refine ⟨fun x => algebraMap ℤ_[l] ↥(OL LL) (w x), fun x => ?_⟩
  have e := congrArg (algebraMap ℤ_[l] ↥(OL LL)) (hw x)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at e
  rw [P.PD_p K, e]
  congr 1
  have hzu : Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom z =
      (H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam := Units.ext hz
  rw [← hzu, ← map_zpow]
  rfl

end Formalism.MainNotions.RamifiedCoefficientChains.S9
