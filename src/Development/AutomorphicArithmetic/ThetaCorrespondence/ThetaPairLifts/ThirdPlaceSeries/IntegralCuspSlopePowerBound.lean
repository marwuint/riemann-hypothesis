import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
namespace UpperTheory.Lit.Tam
end UpperTheory.Lit.Tam
namespace GlobalTheory.SupModel
end GlobalTheory.SupModel
namespace GlobalTheory.LevGeo.RankBd
end GlobalTheory.LevGeo.RankBd
namespace GlobalTheory.LamPet
end GlobalTheory.LamPet
namespace GlobalTheory.LamMuMax
end GlobalTheory.LamMuMax
namespace GlobalTheory
end GlobalTheory
namespace GlobalTheory
end GlobalTheory
namespace GlobalTheory.BergComp
end GlobalTheory.BergComp
namespace GlobalTheory.ConstSzRows
end GlobalTheory.ConstSzRows
namespace GlobalTheory.BergRank
end GlobalTheory.BergRank
namespace GlobalTheory.BergRank
end GlobalTheory.BergRank
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamCore
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem _root_.UpperTheory.Lit.Tam.integral_cusp_slope_power_bound_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ A =>
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.T.lift_weight_numerator)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact UpperTheory.Lit.Tam.slopeMax_sq_latW_le_pow_mul p i trivial hp.2 (a i) (b i) (c i)
end GlobalTheory.CovTop.LamCore
end
end
end
end
