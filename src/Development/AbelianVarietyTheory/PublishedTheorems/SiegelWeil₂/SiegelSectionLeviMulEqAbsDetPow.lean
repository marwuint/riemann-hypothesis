import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open scoped Matrix NNReal TensorProduct Classical ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RegSch

namespace GlobalTheory.Published.SiegelSectionIwasawa

variable {D : D7}

def relat (V : HSp D) (l : Lvl V) (hl : l.Good) : HSp D :=
  { V with
    L0 := l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
    standardTuple_isLattice := by
      have e : l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)) =
          l.L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
        ext x
        constructor
        · intro hx; exact ⟨_, hx, V.frame.equivFun.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          change V.frame.equivFun (V.frame.equivFun.symm y) ∈ l.L
          rwa [LinearEquiv.apply_symm_apply]
      rw [e]
      refine ⟨hl.1.fg.map _, ?_⟩
      change Submodule.span D.host.E (V.frame.equivFun.symm.toLinearMap '' (l.L : Set _)) = ⊤
      rw [← Submodule.map_span, hl.1.span_eq_top, Submodule.map_top, LinearEquiv.range]
    baseLattice_isUnimodular := by
      have h := (SelfDual.forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero hl.1).1 hl.2.1
      have e : ∀ x y, hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := fun x y => by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
        simp only [← Module.Basis.equivFun_apply]
        rfl
      ext z
      have h2 : z ∈ Formalism.HermitianLatticesTheory.dual V.hT (l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
          ∀ x ∈ l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)),
            V.hT x z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
      refine h2.trans (Iff.trans ?_ (h (V.frame.equivFun z)).symm)
      constructor
      · intro H x hx
        obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
        rw [e]
        exact Submodule.mem_one.1 (H x hx)
      · intro H x hx
        rw [← e]
        exact Submodule.mem_one.2 (H _ hx) }

theorem frameLat_relat (V : HSp D) (l : Lvl V) (hl : l.Good) : frameLat (relat V l hl) = l.L := by
  ext y
  exact iff_of_eq (congrArg (· ∈ l.L) (V.frame.equivFun.apply_symm_apply y))

theorem hasIw_of_good {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) : HasIw d l.K := by
  let d' : HypDec (relat V l hl) V₀ r := ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩
  have h := GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D (relat V l hl) V₀ r d' l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2
  intro g
  obtain ⟨q, k, hk, e⟩ := h g
  have e2 : (Kmax (relat V l hl) l.c : Subgroup (GA D V)) = l.K :=
    congrArg (fun L => levelAll D.sp.cm.sig V.gram L l.c) (frameLat_relat V l hl)
  exact ⟨⟨q.1, q.2⟩, k, e2 ▸ hk, e⟩

end GlobalTheory.Published.SiegelSectionIwasawa

end
