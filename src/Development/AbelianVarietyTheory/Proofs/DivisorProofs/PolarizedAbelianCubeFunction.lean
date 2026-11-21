import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Gens

variable {S : Scheme.{0}} {X : Scheme.{0}} (M : LB X) (T : Over S)

def HasGen (F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U)
    (f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T' : Over S) (σ : T' ⟶ T) (p : T'.left) (J : (T'.left ⟶ X) → M.ι), Good M p J → val t σ.left p J = f T' σ p J

variable {M T}

theorem HasGen.mul {F F' : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f f' : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) (h' : HasGen M T F' f') :
    HasGen M T (fun U _ h => F U h * F' U h) (fun T' σ p J => f T' σ p J * f' T' σ p J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen M _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]

theorem HasGen.inv {F : ∀ (U : Type) [CommGroup U], ((T.left ⟶ X) → U) → U}
    {f : ∀ (T' : Over S) (_ : T' ⟶ T) (p : T'.left) (_ : (T'.left ⟶ X) → M.ι), (T'.left.presheaf.stalk p)ˣ}
    (h : HasGen M T F f) :
    HasGen M T (fun U _ h => (F U h)⁻¹) (fun T' σ p J => (f T' σ p J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen M _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun T' σ p J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv _ _ _ _ hJ]

end Gens

end GlobalTheory.WeilIntegral
