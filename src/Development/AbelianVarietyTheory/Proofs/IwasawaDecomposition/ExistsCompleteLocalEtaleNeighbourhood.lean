import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem essFiniteType_int_stalk (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum F := s x
  have h2 : (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hF : Algebra.EssFiniteType ℚ F := inferInstance
  have hZF : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  have h3 : (algebraMap ℤ F).EssFiniteType := RingHom.essFiniteType_algebraMap.2 hZF
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem exists_ringHom_stalk (F : Type) [Field F] (X : Scheme.{0}) (s : X ⟶ Sp F) (x : X) :
    Nonempty (F →+* X.presheaf.stalk x) := by
  let p : PrimeSpectrum F := s x
  exact ⟨(s.stalkMap x).hom.comp (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p))⟩

theorem stalk_factor_eq {X : Scheme.{0}} {R : CommRingCat.{0}} {x y : X} (hy : y = x) (φ : X.presheaf.stalk x ⟶ R)
    (ψ : X.presheaf.stalk y ⟶ R) (h : Spec.map ψ ≫ X.fromSpecStalk y = Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ e : X.presheaf.stalk y →+* X.presheaf.stalk x, Function.Bijective e ∧ ψ.hom = φ.hom.comp e := by
  subst hy
  refine ⟨RingHom.id _, Function.bijective_id, ?_⟩
  have : ψ = φ := Spec.map_injective ((cancel_mono _).1 h)
  subst this
  rfl

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

end GlobalTheory.GenFan
