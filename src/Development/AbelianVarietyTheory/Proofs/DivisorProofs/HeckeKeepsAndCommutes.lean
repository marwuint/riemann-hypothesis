import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeOffLevel

variable {D : D7}

theorem sep_of_offS {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hS : OffS D S Q) (hP : PP.under (𝓞 D.host.F) ∈ S) : PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
  obtain ⟨x, hx, hQ⟩ := hS _ hP
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  refine ⟨fun h => hQ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl (h ▸ hx'), fun h => ?_⟩
  obtain ⟨c, hc, e⟩ := h _ hx'
  exact hQ c (e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)) hc

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_mul : ∀ k ∈ Lev.levG V β L, ∀ k' ∈ Lev.levG V β L,
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  intro k hk k' hk'
  unfold Lev.levChi
  rw [MonoidHom.map_mul, ← Units.val_mul]
  exact congrArg Units.val ((levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {Rp : Finset (GA D V)}

theorem hasType_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) {Φ : GA D V → ℂ}
    (hΦ : Lev.HasType V β L Φ) : Lev.HasType V β L (heckeLin V Rp Φ) :=
  GlobalTheory.SphericalOps.level_heckeLin levChi_mul
    (fun e f _ hi => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 Q e f hi hN hP).2.2) h hΦ

end GlobalTheory.HeckeOffLevel
