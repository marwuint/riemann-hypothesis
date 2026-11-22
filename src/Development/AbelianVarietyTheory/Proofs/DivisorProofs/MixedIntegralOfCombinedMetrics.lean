import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

end GlobalTheory.CombChern
