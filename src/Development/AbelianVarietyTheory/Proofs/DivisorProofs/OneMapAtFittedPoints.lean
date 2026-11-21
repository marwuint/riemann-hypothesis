import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMatrixDescendsOfRationalOnTuple
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem out_sum_tw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {n : ℕ}
    (f : E →ₗ[ℂ] ℂ) (φ : (Fin n → ℂ) →ₗ[ℂ] Tw s E) (z : Fin n → ℂ) :
    f (Tw.out (φ z)) = ∑ k, cj s (z k) * f (Tw.out (φ (Pi.single k 1))) := by
  let o : Tw s E →+ E := ⟨⟨Tw.out, rfl⟩, Tw.out_add⟩
  have e : z = ∑ k, z k • (Pi.single k 1 : Fin n → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j; by_cases hj : j = k <;> simp [hj]
  conv_lhs => rw [e, map_sum]
  rw [show Tw.out (∑ k, φ (z k • Pi.single k 1)) = ∑ k, Tw.out (φ (z k • (Pi.single k 1 : Fin n → ℂ))) from
    map_sum o (fun k => φ (z k • (Pi.single k 1 : Fin n → ℂ))) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Tw.out_smul, map_smul, smul_eq_mul]

theorem twist_conj_base_embedding_eq (p : PtAt ex Csz) (a : D.what₂.LL) :
    cj (twAt D.what₂.embLL p.P.A3.A.v0) (p.P.A3.fam3.base3.v0.embedding a) = D.what₂.embLL a := by
  rw [show p.P.A3.fam3.base3.v0 = p.P.A3.A.v0 from rfl, emb_eq D.what₂.embLL p.P.A3.A.v0 a, cj_cj, sgAt_mk _ p.R.hv0]

theorem mul_eq_one_of_covolume_identity (κ zt z0 ct c0 v : ℂ) (hκ : κ ≠ 0) (hzt : zt ≠ 0) (hz0 : z0 ≠ 0) (hct : ct ≠ 0) (hc0 : c0 ≠ 0) :
    κ⁻¹ * z0 * c0 * (κ * v / (zt * ct)) = (zt / z0 * (ct / c0))⁻¹ * v := by
  field_simp

end GlobalTheory.BigTop.Fun
