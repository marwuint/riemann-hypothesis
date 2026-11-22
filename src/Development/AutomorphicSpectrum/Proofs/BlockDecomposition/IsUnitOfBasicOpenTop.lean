import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.BaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers CompanionTheory.KM.G4 ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

def Sc.A (S : Sc Φ Λ) : C ⥤ CommAlgCat.{0} Λ where
  obj T := letI := (S.ρ T).toAlgebra; CommAlgCat.of Λ (Φ.A.obj T)
  map {T T'} f :=
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T').toAlgebra
    CommAlgCat.ofHom { (Φ.A.map f).hom.toRingHom with commutes' := S.nat f }
  map_id T := by
    letI := (S.ρ T).toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_id T)
  map_comp {T T' T''} f g := by
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T'').toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_comp f g)

def Sc.site (S : Sc Φ Λ) : PDF Λ C where
  A := S.A
  J := ⟨fun T => Φ.J.S T, fun φ _ hx => Φ.J.map_mem φ hx⟩
  dp {T} k x := Φ.dp (T := T) k x
  dp_zero := Φ.dp_zero
  dp_one := Φ.dp_one
  dp_zero_right := Φ.dp_zero_right
  dp_add := Φ.dp_add
  dp_map φ := Φ.dp_map φ

def Sc.poly (S : Sc Φ Λ) (Q : Poly Φ) : Poly S.site where
  P := Q.P
  j := Q.j
  X := Q.X
  X_mem := Q.X_mem
  univ := Q.univ
  span := Q.span

def Sc.loc (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) :
    Sc (Φ.res G) (Localization.Away Y) where
  ρ T := IsLocalization.Away.lift Y (hu T)
  nat {T T'} φ a := by
    have e : ((Φ.A.map (G.map φ)).hom.toRingHom).comp (IsLocalization.Away.lift Y (hu T)) =
        IsLocalization.Away.lift (S := Localization.Away Y) Y (hu T') := by
      refine IsLocalization.ringHom_ext (Submonoid.powers Y) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
      exact S.nat (G.map φ) a
    exact RingHom.congr_fun e a

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
end GlobalTheory.CompanionTheory.KMVan
