import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ParMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLocalInputs

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
structure HypAAlt : Prop where
  a1 : GlobalTheory.NT.RayField
  a2 : GlobalTheory.Published.PrincipalIdealSt
  a3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  a5 : GlobalTheory.Published.HarishChandraModules
  a6 : GlobalTheory.Published.CuspRapidDecay
  a7 : GlobalTheory.Published.CasselmanWallach
  a8 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  a9 : GlobalTheory.Published.DiscreteSeriesExists
  a10 : GlobalTheory.Published.HarishChandraFinite
  a11 : GlobalTheory.Dec.DSInfChar
  a12 : GlobalTheory.Published.DiscreteSeriesUpqUnique
  a13 : Formalism.L2.SG.RowsDef.RowsFinDim
  a14 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  a16 : Vol.DiscreteSeriesExist
  a17 : Vol.FormalDegreeFormula₂
  a18 : StandardLattice.SiegelMassRatioCM
  a19 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ
  a20 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)
  a21 : ∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam
  a22 : GlobalTheory.Published.GlobalArtinReciprocity
  a23 : GlobalTheory.Published.WeberRayFieldSt
end
end GlobalTheory.Mem.Top.Bl
end
end
