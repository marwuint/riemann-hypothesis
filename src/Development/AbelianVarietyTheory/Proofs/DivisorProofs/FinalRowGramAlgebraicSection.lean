import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdeal
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR

theorem hatL_cong_of_hat {D : D7} (V : HSp D) (κ : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin V.rank → D.host.E))) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V κ).1 *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz))
  have e : (Lev.finE V κ).1 = (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F _ D.host.E) := rfl
  convert h1 using 1
  funext j
  rw [e]
  simp only [Pi.sub_apply, map_sub, Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply,
    Matrix.map_apply]

end GlobalTheory.BaseLevelInj

