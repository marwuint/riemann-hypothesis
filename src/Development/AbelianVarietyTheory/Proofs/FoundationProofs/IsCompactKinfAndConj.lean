import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1

end GlobalTheory.Cusp.KinfCompact

end
