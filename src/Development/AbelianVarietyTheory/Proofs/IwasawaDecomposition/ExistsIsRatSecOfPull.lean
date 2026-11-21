import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import ReciprocityTheory.GaloisValuations.GlobalB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

end GlobalTheory.TrueGeo.SmallSec
