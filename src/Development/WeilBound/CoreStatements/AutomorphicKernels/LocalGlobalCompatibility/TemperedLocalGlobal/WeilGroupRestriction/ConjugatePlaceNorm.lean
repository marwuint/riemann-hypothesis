import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.WeilBound.CoreStatements.SatakeConjugation.CsdIff
import Development.WeilBound.CoreStatements.SatakeConjugation.CsdDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.CuspRep

namespace PositivityTheory.Pf1.CLGD.K

namespace ConjugatePlaceNorm

theorem satFlip : PositivityTheory.NCmp.SatFlip := by
  intro L _ _ _ a π π' T hT w B hB
  let Tθ : π.V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub π).V := (GlobalTheory.ThetaPull.pull L a).submoduleMap π.V
  have hTθ : ∀ o φ, Tθ (π.op (thetaOp o) φ) = (GlobalTheory.ThetaPull.thetaSub π).op o (Tθ φ) :=
    fun o φ => Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm
  have hI : CuspSub.Iso (GlobalTheory.ThetaPull.thetaSub π) π' := by
    refine ⟨Tθ.symm.trans T, fun o ψ => ?_⟩
    obtain ⟨φ, rfl⟩ := Tθ.surjective ψ
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hTθ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, hT]
  have hiso : CG.mk (GlobalTheory.ThetaPull.thetaSub π) = CG.mk π' := Quotient.sound hI
  have e : conjSrc (IsCMField.complexConj L).toRingEquiv (conjSrc (IsCMField.complexConj L).toRingEquiv w) = w :=
    GlobalTheory.ThetaPull.conjSrc_conjSrc w
  have hB' : (CG.mk π).HasSat (conjSrc (IsCMField.complexConj L).toRingEquiv
      (conjSrc (IsCMField.complexConj L).toRingEquiv w)) B := by rw [e]; exact hB
  have h1 := GlobalTheory.ThetaSatake.hasSat_thetaSub π (conjSrc (IsCMField.complexConj L).toRingEquiv w) B hB'
  rw [hiso] at h1
  exact h1

theorem hasSat_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} (π : CuspSub L a) (hc : π.IsCsd)
    (w : HeightOneSpectrum (𝓞 L)) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    (CG.mk π).HasSat (conjSrc (PositivityTheory.NCmp.cc L) w) (B.map (·⁻¹)) :=
  PositivityTheory.NCmp.sat_conj_of_isCsd satFlip (CG.mk π) hc w B hB

end ConjugatePlaceNorm

end PositivityTheory.Pf1.CLGD.K

end
