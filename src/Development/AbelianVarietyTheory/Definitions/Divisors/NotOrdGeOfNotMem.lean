import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def ThroughU {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (T : Trait F) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ ≫ c = T.y

variable {M}

theorem OrdGe.mul {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ} (hx : OrdGe M T ξ x a) (hy : OrdGe M T ξ y b) :
    OrdGe M T ξ (x * y) (a + b) := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  have hsp : ∀ v, (jK T.V ≫ ξ) v ⤳ (jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V)) := fun v => by
    rw [Subsingleton.elim v (IsLocalRing.closedPoint (FractionRing T.V))]
  refine ⟨Subalgebra.mul_mem _ hx0 hy0, w * w', ?_⟩
  rw [RatModel.val_mul hsp hx0 hy0, hw, hw', ← map_mul, pow_add]
  congr 1
  ring

variable (M)

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def TraitUniqSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T T' : Trait F) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (f : T.V →+* W) (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W)
    (fK' : FractionRing T'.V →+* FractionRing W), GlobalTheory.Mum.Base W → IsDiscreteValuationRing W →
    Function.Injective f → Function.Injective f' → IsLocalHom f → IsLocalHom f' →
    (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) →
    spMap fK ≫ T.y = spMap fK' ≫ T'.y → ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) →
      Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.D.toPre.X ≃+ T'.D.toPre.X, ∀ a b, (m : ℤ) * T.β a b = m' * T'.β (e a) (e b)

end GlobalTheory.Poinc
