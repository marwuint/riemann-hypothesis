import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def IsTest (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (yb : Sp 𝓞_ℂ_[p] ⟶ X) : Prop :=
  (∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb) ∧
    Set.range (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ⊆ Xw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Lie

variable {X : Scheme.{0}} (t : SAB H X) {g m : ℕ}

def IsEigG {S : Type} [CommRing S] (σ : 𝓞 E →+* S) (u : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∀ a, u ≫ (t.act.act a).left = spMap (epsMul (σ a)) ≫ u

def EigRowsAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin m → Fin g → S) : Prop :=
  ∀ k u, IsCombAtG t x e (U k) u → IsEigG t σ u

def bcV {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    Fin g → (Sp (DualNumber S) ⟶ t.G.left) := fun i => spMap (dualMap φ) ≫ e i

end Lie

section BaseChange

variable {X : Scheme.{0}} {t : SAB H X} {g : ℕ} {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']

theorem bcV_bcV (φ : R →+* S) (ψ : S →+* S') (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    bcV t ψ (bcV t φ e) = bcV t (ψ.comp φ) e := by
  funext i
  rw [bcV, bcV, bcV, ← Category.assoc, spMap_spMap]
  congr 2
  ext s <;> simp [dualMap]

theorem sp_sp (φ : R →+* S) (ψ : S →+* S') (x : Sp R ⟶ X) : spMap ψ ≫ spMap φ ≫ x = spMap (ψ.comp φ) ≫ x := by
  rw [← Category.assoc, spMap_spMap]

theorem isTanBasis_bc {x : Sp R ⟶ X} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x e)
    (φ : R →+* S) : IsTanBasis t (spMap φ ≫ x) (bcV t φ e) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun S' _ ψ w hw => ?_⟩
  · rw [bcV, Category.assoc, (h.1 i).1, sp_sp, sp_sp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · have e1 : (1 : Over.mk (spMap φ ≫ x) ⟶ t.G) = (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [e1, Over.comp_left, ← (h.1 i).2, bcV, ← Category.assoc, spMap_spMap]
    change _ = spMap φ ≫ _ ≫ _
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sp_sp] at hw ⊢
    have := h.2 S' (ψ.comp φ) w hw
    change ∃! a, IsCombAtG t _ (bcV t ψ (bcV t φ e)) a w
    rw [bcV_bcV]
    exact this

theorem bot_map [IsDomain R] [IsDomain S] {φ : R →+* S} (hφ : Function.Injective φ) (x : Sp R ⟶ X) :
    (spMap φ ≫ x) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) = x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg x ?_)
  exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot φ).1 hφ)

end BaseChange

end GlobalTheory.FlatModel

end
