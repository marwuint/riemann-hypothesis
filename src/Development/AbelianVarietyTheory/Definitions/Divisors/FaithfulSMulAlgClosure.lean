import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus

section Bplus

abbrev BplusIn (A K : Type) [CommRing A] [Field K] [Algebra A K] : Type := integralClosure A K

theorem faithfulSMul_algClosure (A F : Type) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F] :
    FaithfulSMul A (AlgebraicClosure F) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq A F (AlgebraicClosure F)]
    exact (algebraMap F (AlgebraicClosure F)).injective.comp (IsFractionRing.injective _ _)

theorem isAlgebraic_algClosure (A F : Type) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] :
    Algebra.IsAlgebraic A (AlgebraicClosure F) :=
  (IsFractionRing.comap_isAlgebraic_iff (K := F)).2 inferInstance

instance (A : Type) [CommRing A] [IsDomain A] : FaithfulSMul A (AlgebraicClosure (FractionRing A)) :=
  faithfulSMul_algClosure A _

instance (A : Type) [CommRing A] [IsDomain A] : Algebra.IsAlgebraic A (AlgebraicClosure (FractionRing A)) :=
  isAlgebraic_algClosure A _

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

instance isFractionRing [IsDomain A] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] : IsFractionRing (BplusIn A K) K :=
  integralClosure.isFractionRing_of_algebraic fun _ hx => FaithfulSMul.algebraMap_injective A K (hx.trans (map_zero _).symm)

instance isIntegrallyClosed [IsDomain A] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] : IsIntegrallyClosed (BplusIn A K) :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn K).2 inferInstance

variable {A K}

def incl {A' : Type} [CommRing A'] [Algebra A' K] (φ : A →+* A') (h : ∀ a, algebraMap A' K (φ a) = algebraMap A K a) :
    BplusIn A K →+* BplusIn A' K :=
  (integralClosure A K).val.toRingHom.codRestrict (integralClosure A' K) fun x =>
    IsIntegral.map_of_comp_eq φ (RingHom.id K) (RingHom.ext h) x.2

@[simp] theorem coe_incl {A' : Type} [CommRing A'] [Algebra A' K] (φ : A →+* A')
    (h : ∀ a, algebraMap A' K (φ a) = algebraMap A K a) (x : BplusIn A K) : (incl φ h x : K) = x := rfl

end Bplus

section Opens

variable (X : Scheme.{0}) [IsIntegral X]

abbrev Kbar : Type := AlgebraicClosure X.functionField

def AffOp : Type := {U : X.Opens // IsAffineOpen U ∧ Nonempty U}

variable {X}

instance (U : AffOp X) : Nonempty U.1 := U.2.2

instance (U : AffOp X) : IsFractionRing Γ(X, U.1) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U.1 U.2.1

instance (U : AffOp X) : FaithfulSMul Γ(X, U.1) (Kbar X) := faithfulSMul_algClosure _ _

instance (U : AffOp X) : Algebra.IsAlgebraic Γ(X, U.1) (Kbar X) := isAlgebraic_algClosure _ _

abbrev AffOp.Bp (U : AffOp X) : Type := BplusIn Γ(X, U.1) (Kbar X)

def AffOp.res {U U' : AffOp X} (h : U'.1 ≤ U.1) : U.Bp →+* U'.Bp :=
  incl (resG X h) fun a => congrArg (algebraMap X.functionField (Kbar X))
    (X.presheaf.germ_res_apply (homOfLE h) _ _ a)

end Opens

section TorsionMap

variable {p : ℕ} {O : Type} [CommRing O]

abbrev Tors (A : Over (Sp O)) [GrpObj A] (N : ℕ) (B : Type) [CommRing B] [Algebra O B] : Type :=
  {z : SpAlg O B ⟶ A // z ^ N = 1}

structure TorsionMap (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) : Type 1 where

  pt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B], Tors A (p ^ n) B → (G.A n →ₐ[O] B)

  nat : ∀ (n : ℕ) (B C : Type) [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : B →ₐ[O] C)
    (z : Tors A (p ^ n) B) (z' : Tors A (p ^ n) C), z'.1 = spOver φ ≫ z.1 → pt n C z' = φ.comp (pt n B z)

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (x y z : Tors A (p ^ n) B), z.1 = x.1 * y.1 →
    toConv (pt n B z) = toConv (pt n B x) * toConv (pt n B y)

  res : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (z : Tors A (p ^ n) B) (z' : Tors A (p ^ (n + 1)) B), z'.1 = z.1 →
    pt (n + 1) B z' = (pt n B z).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)

variable {A : Over (Sp O)} [GrpObj A] {G : PDivGroup p O}

theorem isTangent_iff_lieG (v : epsR O ⟶ A) : IsTangent v ↔
    Pdiv.ptMap (TrivSqZeroExt.fstHom O O O) ≫ (v : Pdiv.specO O (DualNumber O) ⟶ A) = toUnit (Pdiv.specO O O) ≫ η[A] := by
  have h' : (toUnit (Pdiv.specO O O)).left = 𝟙 (Sp O) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, h']
  exact ⟨fun h => h.trans (Category.id_comp _).symm, fun h => h.trans (Category.id_comp _)⟩

theorem isTangent_lieG (x : Pdiv.LieG A) : IsTangent (G := A) x.1 := (isTangent_iff_lieG _).2 x.2

def tanTors (p n : ℕ) (x : Pdiv.LieG A) : Tors A (p ^ n) (DualNumber (ModPow p O n)) :=
  ⟨epsRedPow p n x.1, epsRedPow_pow (isTangent_lieG x) n⟩

namespace TorsionMap

variable (θ : TorsionMap A G)

def IsOpenNearZero : Prop :=
  ∀ n, ∃ (U : A.left.Opens) (V : (Sp (G.A n)).Opens), Set.range η[A].left ⊆ U ∧
    ∀ (B : Type) [CommRing B] [Algebra O B], Set.BijOn (θ.pt n B) {z | Set.range z.1.left ⊆ U}
      {φ | Set.range (spMap (φ : G.A n →+* B)) ⊆ V}

def IsIsoOver (W : Set (Sp O)) : Prop :=
  ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B], Set.range (spMap (algebraMap O B)) ⊆ W → Function.Bijective (θ.pt n B)

def IsOmegaAt (n : ℕ) (c : Pdiv.omega A →ₗ[O] Cot O (G.A n)) : Prop :=
  Function.Surjective c ∧ (∀ w, c w = 0 ↔ ∃ w', w = (p : O) ^ n • w') ∧
    ∀ (x : Pdiv.LieG A) (w : Pdiv.omega A) (a : G.A n), dUnit O a = c w →
      (θ.pt n _ (tanTors p n x) a).snd = Ideal.Quotient.mk _ (w.1 x)

def IsOmega (c : Pdiv.omega A →ₗ[O] G.omega) : Prop :=
  ∀ n, θ.IsOmegaAt n ((LinearMap.proj n ∘ₗ G.omegaSub.subtype) ∘ₗ c)

def Intertwines (f : A ⟶ A) (g : G ⟶ G) : Prop :=
  ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (z z' : Tors A (p ^ n) B), z'.1 = z.1 ≫ f →
    θ.pt n B z' = (θ.pt n B z).comp (g.app n : G.A n →ₐ[O] G.A n)

def ofTower (t : G.TorsionTower A) : TorsionMap A G where
  pt n B _ _ z := t.lift n z.1 z.2
  nat n B C _ _ _ _ φ z z' h := t.inj n C _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y, h])
  mul n B _ _ x y z h := t.pts_injective n B (by rw [map_mul]; simp only [TorsionTower.pts_apply, t.lift_y, h])
  res n B _ _ z z' h := t.inj (n + 1) B _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.res, t.lift_y, h])

theorem ofTower_tanTors (t : G.TorsionTower A) (n : ℕ) (x : Pdiv.LieG A) :
    (ofTower t).pt n _ (tanTors p n x) = t.tanPt (isTangent_lieG x) n := rfl

end TorsionMap

end TorsionMap

section PropG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {p : ℕ} [Fact p.Prime]
  {R : Type} [CommRing R]

abbrev tatePt {G : PDivGroup p R} (s : G.Tate) (n : ℕ) (B : Type) [CommRing B] [Algebra R B] : G.A n →ₐ[R] B :=
  (Algebra.ofId R B).comp (s.pt n)

structure IsPropG (t : SAB H (Sp R)) (GG : PDivGroup p R) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual)
    (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p R).Tate) (τ : Dw.La →+ GG.Tate) : Prop where

  height : GG.height = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))

  equivariant : ∀ a, θ.Intertwines (t.act.act a) (act a)

  interior : θ.IsIsoOver (abLocus t.G)

  nearZero : θ.IsOpenNearZero

  omega : ∃ c : Pdiv.omega t.G →ₗ[R] GG.omega, θ.IsOmega c ∧ ∀ (a : 𝓞 E) (w w' : Pdiv.omega t.G),
    (∀ x x' : Pdiv.LieG t.G, x'.1 = x.1 ≫ t.act.act a → w'.1 x = w.1 x') → c w' = omegaMap GG GG (act a) (c w)

  adj : ∀ a, (act a : GG ⟶ GG) ≫ pol.hom = pol.hom ≫ dualHom GG GG (act (H.bar a))

  skew : GG.bidual.hom ≫ dualHom GG GG.dual pol.hom = -pol.hom

  prim : ∀ n, IsPrimitiveRoot (muRoot ε n) (p ^ n)

  lin : ∀ (a : 𝓞 E) (x : Dw.La), τ (a • x) = tateMap GG GG R (act a) (τ x)

  pair : ∀ x y, pairing GG R (τ x) (tateMap GG GG.dual R pol.hom (τ y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • ε

  onto : ∀ (n : ℕ) (k : Type) [Field k] [Algebra R k], (p : k) ≠ 0 → ∀ φ : GG.A n →ₐ[R] k, ∃ x, tatePt (τ x) n k = φ

  weil : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra R k], (p : k) ≠ 0 →
    Set.range (spMap (algebraMap R k)) ⊆ abLocus t.G → ∀ (x x' : Tors t.G (p ^ n) k) (y : Dw.La) (u : kˣ),
      θ.pt n k x' = tatePt (τ y) n k → (u : k) = θ.pt n k x (charElem (tateMap GG GG.dual R pol.hom (τ y)) n) →
        Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u)

variable {Dw}

def dualVec {J : Type} (b : Module.Basis J ℤ Dw.La) (j : J) : Dw.La := -(Dw.unimod.2 (b.coord j)).choose

theorem EF_dualVec {J : Type} (b : Module.Basis J ℤ Dw.La) (x : Dw.La) (j : J) : Dw.EF x (dualVec b j) = b.repr x j := by
  rw [dualVec, map_neg, LinearMap.IsAlt.neg Dw.alt, (Dw.unimod.2 (b.coord j)).choose_spec, Module.Basis.coord_apply]

namespace IsPropG

variable {t : SAB H (Sp R)} {GG : PDivGroup p R} {act : Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG}
  {ε : (PDivGroup.mu p R).Tate} {τ : Dw.La →+ GG.Tate} (h : IsPropG Dw t GG act pol θ ε τ)

def constTate (b : Module.Basis (Fin GG.height) ℤ Dw.La) : ConstTate ε GG where
  t i := τ (b i)
  t' j := tateMap GG GG.dual R pol.hom (τ (dualVec b j))
  pair i j := by
    rw [h.pair, EF_dualVec, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

end IsPropG

end PropG

end GlobalTheory.GroupBplus

end
