import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OntoOfSurjectiveDescents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

end GlobalTheory.ChainOnto.Model

end
