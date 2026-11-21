import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitNatCastOfLeGenO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagAtOfFlagAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBLatLBAndTrAdd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.EigenSplit GlobalTheory.FlagPts GlobalTheory.TotalFrame
open GlobalTheory.CechPic (cls)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hL : HasLatFlags Z L)

include hp hW hL

theorem HasLatFlags.isTr_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    q.IsTr q' e (q.tr q' e).val :=
  LatChart.isTr_tr (LatChart.existsUnique_isTr E H Dw Xo p W hp hW Y i₀ Z B L hL.1 q q' e).exists

theorem HasLatFlags.isLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : (latLB Z L e).IsLB :=
  (LatGr.isLB_latLB_and_tr_add E H Dw Xo p W hp hW Y i₀ Z B L hL fun q q' e => ⟨_, hL.isTr_tr hp hW q q' e⟩).1 e

def HasLatFlags.latCls : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ CechPic.Pic Z.X :=
  AddMonoidHom.mk' (fun e => cls _ (hL.isLB hp hW e)) fun e e' => by
    have h := CechPic.isLB_tens (hL.isLB hp hW e) (hL.isLB hp hW e')
    refine (CechPic.cls_eq_iff _ h).2 (CechPic.iso_of_chart h ⟨fun c => (c, c), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' => ?_⟩)
    refine .trans ?_ (CechPic.gm_tens (latLB Z L e) (latLB Z L e') (𝟙 _) y (c, c) (c', c') ⟨hc, hc⟩ ⟨hc', hc'⟩).symm
    exact (congrArg _ ((LatGr.isLB_latLB_and_tr_add E H Dw Xo p W hp hW Y i₀ Z B L hL
      fun q q' e => ⟨_, hL.isTr_tr hp hW q q' e⟩).2 c c' e e')).trans (map_mul _ _ _)

def HasLatFlags.degHom {k : Type} [Field k] (c : Curve k Z.X) : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ ℤ :=
  c.degPic.comp (hL.latCls hp hW)

theorem HasLatFlags.degHom_apply {k : Type} [Field k] (c : Curve k Z.X) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    hL.degHom hp hW c e = c.degLat L e := rfl

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

def crhTrue : CrHSt ct (flgTrue ct) := crhOf ct (IsHTLatOf (htmTrue ct)) (HTm.htFam ct)

namespace HTm

abbrev flagMdl (Z : ct.Mdl) : ct.Mdl := ct.flagCl Z (htFam ct Z).1

abbrev htLat (Z : ct.Mdl) : Lat Z := FlagFam.lat (htFam ct Z)

variable {ct} {Z : ct.Mdl} {n : ℕ}

theorem degGr_eq (c : Curve ct.Fbar (flagMdl ct Z).X) (τ : PsiT D) (i : ℕ) :
    (crhTrue ct).degGr (Z := Z) c τ i = c.degLat (htLat ct Z) (-ct.expo (At.indWt τ i)) := rfl

end HTm

namespace At

end At

end GlobalTheory.LocM
