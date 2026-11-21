import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta

noncomputable section
namespace GlobalTheory.ArcDictModel
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HostModel

section Bridge
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

theorem nonempty_of_frameValues (Λ : letI := H.starRing; ArcPts.GtAn a) : Nonempty (GtAn a) := by
  letI := H.starRing
  have h := fun (j : ℕ) (hj : NeZero j) (α : Λ.A.X) =>
    TwistedTheta.sections_equiv_anArc_theta Λ.A a.D₀ Λ.u _ Λ.lam (fun _ _ e => congrArg Λ.A.chi (Subtype.ext e)) Λ.ah j
      (Nat.one_le_iff_ne_zero.2 hj.out) (fun θ hθ => ((Λ.pow j).2 θ hθ).exists) (Λ.ε α) α (Λ.ct α)
  choose e _ he using h
  refine ⟨⟨⟨GtAnModel.toDict Λ, fun x y => (Λ.be_eq x y).symm⟩, ⟨fun j hj α => (e j hj α).toEquiv, ?_⟩⟩⟩
  intro j hj α s z i hi
  refine (he j hj α s z i hi).trans (congrArg (_ * ·) ?_)
  refine Eq.trans ?_ (Fin.prod_univ_four _).symm
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _).symm) (zpow_neg_one _).symm)
    (zpow_one _).symm

end Bridge

end GlobalTheory.ArcDictModel
