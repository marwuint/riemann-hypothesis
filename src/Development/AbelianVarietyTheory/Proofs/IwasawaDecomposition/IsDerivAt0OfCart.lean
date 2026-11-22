import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorFrHolo

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)

theorem isDerivAt0_of_cart {g : ℕ} {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) (pt : Sp ℂ ⟶ X') {e : (Fin g → ℂ) → (Sp ℂ ⟶ G')} (he : ∀ z, e z ≫ h' = pt)
    (hol : IsHolTo Set.univ fun z => e z ≫ φ) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'}
    (hv : v ≫ h' = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ pt) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  have H := (IsPullback.of_hasPullback h' pt).paste_horiz hc
  have key := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp]))
    (fun z => pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hol)
    (v := pullback.lift v _ hv) (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using isDerivAt0_comp_hom key (pullback.fst h' pt)

theorem isHolTo_lift {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) {n g : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (a : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (ha : IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => a bz.1 bz.2) (hp : IsHolTo B p)
    (w : ∀ b z, a b z ≫ h = p b ≫ f) :
    IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => hc.lift (a bz.1 bz.2) (p bz.1) (w _ _) := by
  let L : (Fin (n + g) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin g → ℂ) :=
    ((LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin g) ℂ ℂ)).toContinuousLinearEquiv
  have hC : IsOpen (L ⁻¹' (B ×ˢ Set.univ)) := (hB.prod isOpen_univ).preimage L.continuous
  have h1 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => a (L c).1 (L c).2 :=
    LocLift.isHolTo_comp ha hC L.differentiableOn fun _ h => h
  have h2 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => p (L c).1 :=
    LocLift.isHolTo_comp hp hC (β := fun c => (L c).1) (by fun_prop) fun _ h => h.1
  have h3 := holPair _ _ _ h f _ _ _ _ (fun c => w (L c).1 (L c).2) hC h1 h2
  have h4 := isHolTo_comp h3 hc.isoPullback.inv
  have key : ∀ c, pullback.lift (a (L c).1 (L c).2) (p (L c).1) (w _ _) ≫ hc.isoPullback.inv =
      hc.lift _ _ (w (L c).1 (L c).2) := fun c => hc.hom_ext
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.lift_fst]
      exact pullback.lift_fst _ _ _)
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.lift_snd]
      exact pullback.lift_snd _ _ _)
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h4 ((hB.prod isOpen_univ)) (β := L.symm)
    L.symm.differentiableOn fun q hq => by simpa using hq) fun q _ => ?_
  refine Eq.trans ?_ (key (L.symm q)).symm
  simp only [L.apply_symm_apply]

end GlobalTheory.TrueCx.TorFrHolo
