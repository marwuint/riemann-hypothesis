import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_pow {X Z : Scheme.{0}} [IsIntegral Z] (B : LB X) (j : Z ⟶ X) (m : ℕ)
    {r : (B.pull j).ι → Z.functionFieldˣ} (hr : IsRatSec (B.pull j) r) :
    IsRatSec ((lbPow B m).pull j) fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m := by
  intro i i' h
  have l₀ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U fun _ => i' PUnit.unit PUnit.unit :=
    fun _ hx => ⟨InducedPow.mem_chart B j m hx.1, InducedPow.mem_chart B j m hx.2⟩
  have l₁ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      j ⁻¹ᵁ ((lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₂ : (lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit) ≤
      B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₃ : (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U (fun _ => i' PUnit.unit PUnit.unit) ≤
      j ⁻¹ᵁ (B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr _ _ (l₀ h), mul_pow,
    InducedPow.pull_g _ j i i' l₁, InducedPow.pow_g B m _ _ l₂, map_pow, map_pow,
    InducedPow.pull_g B j _ _ l₃, ← fnOf_resG l₀ h]
  congr 3
  have e : j.appLE _ _ l₃ ≫ Z.presheaf.map (homOfLE l₀).op =
      X.presheaf.map (homOfLE l₂).op ≫ j.appLE _ _ l₁ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom (B.g (i PUnit.unit PUnit.unit) (i' PUnit.unit PUnit.unit)).val) e

end GlobalTheory.CoverNorm
