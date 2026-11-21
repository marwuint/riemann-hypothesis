import Development.WeilBound.CoreStatements.SatakeConjugation.CsdDefs

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

abbrev cc (L : Type) [Field L] [NumberField L] [IsCMField L] : L ≃+* L := (IsCMField.complexConj L).toRingEquiv

theorem conjSrc_conjSrc (v : HeightOneSpectrum (𝓞 L)) : conjSrc (cc L) (conjSrc (cc L) v) = v := by
  have h1 := conjPl_conjSrc (cc L) v
  have h2 : GlobalTheory.Mem.Chr.ConjPl (cc L) v (conjSrc (cc L) v) := fun x => by
    have := h1 (cc L x)
    simp only [cc, AlgEquiv.coe_ringEquiv, IsCMField.complexConj_apply_apply] at this ⊢
    exact this.symm
  exact (eq_conjSrc h2).symm

theorem sat_conj_of_isCsd (hS : SatFlip) {a : ℕ} (π : CG L a) (h : π.IsCsd) (w : HeightOneSpectrum (𝓞 L))
    (B : Multiset ℂˣ) (hB : π.HasSat w B) : π.HasSat (conjSrc (cc L) w) (B.map (·⁻¹)) := by
  induction π using Quotient.inductionOn with
  | _ π0 =>
    obtain ⟨T, hT⟩ := h
    exact hS L a π0 π0 T hT w B hB

end PositivityTheory.NCmp
