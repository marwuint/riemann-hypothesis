import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7}

section Same

theorem lat_of_heq {r j p r' j' : ℕ} {Λ : ModuliIntegralCharts.Loc D r j p} {Λ' : ModuliIntegralCharts.Loc D r' j' p} (hr : r = r') (hj : j = j')
    (hΛ : HEq Λ Λ') {y : Λ.Pt Λ.YY} {y' : Λ'.Pt Λ'.YY} (hy : HEq y y') {Y : Type} [AddCommGroup Y]
    [Module (𝓞 D.host.E) Y] (β : Y → Y → ℝ)
    (hY : ∃ e : Λ.Ylat y ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ.be y a b) :
    ∃ e : Λ'.Ylat y' ≃ₗ[𝓞 D.host.E] Y, ∀ a b, β (e a) (e b) = Λ'.be y' a b := by
  subst hr hj; cases hΛ; cases hy; exact hY

end Same

section Comparison₂

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

def LocTie : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p,
  HEq (T.G.P.loc (T.G.dat j) p) ((k.at (datW D F.κg j)).pad.loc p)

variable {h t K R k}

theorem rk_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.rk (T.G.dat j) = (datW D κ j).N :=
  (h.datum_condition j h1 hm).1.trans (datW_N D κ j).symm

theorem jj_dat_eq (h : LawsP T) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) :
    T.G.P.jj (T.G.dat j) = (datW D κ j).j :=
  (h.datum_condition j h1 hm).2.trans (datW_j D κ h1 hm.le).symm

theorem LocTie.lat (H : LocTie h k) {j : ℕ} (h1 : 1 ≤ j) (hm : j < D.R.m) {la : HeightOneSpectrum (𝓞 T.Q.c.F)}
    {z : PointsOfFlagModel.Pt (T.G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : T.G.IsAlgPt j la z) {η : T.G.PY j (WeightAlgebra.resCh la)}
    (hr : T.G.rel j _ η z)
    {η' : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Pt ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).YY}
    (he : HEq η η') (A : DatAt ((T.G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    ∃ e : ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).Ylat η' ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = ((k.at (datW D F.κg j)).pad.loc (WeightAlgebra.resCh la)).be η' a b :=
  lat_of_heq (rk_dat_eq h F.κg h1 hm) (jj_dat_eq h F.κg h1 hm) (H j h1 hm _) he (fun a b => A.beta a b)
    (h.lattice_condition j h1 hm la z hz η hr A)

end Comparison₂

end GlobalTheory.ShFam
