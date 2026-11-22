import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

namespace Sep
open GlobalTheory.ZH

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def IsAct (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) : Prop :=
  IsDiagEnd F W X₁.ρ.P X₁.u act

theorem IsAct.isMonHom {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (h : IsAct X₁ act)
    (E : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (act E) := by
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := h
  have key : ∀ (T' : Over (Sp X₁.S.R)) (x : T' ⟶ X₁.ρ.P.A) (a : Fin 8),
      (x ≫ act E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun b _ => map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => (huniq T' fun a => (x ≫ act E * z ≫ act E) ≫ pr a).unique (fun a => ?_) fun _ => rfl
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ X₁.ρ.P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  rw [key, hm, key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

structure UMem (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
    (X : Type) [AddCommGroup X] {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) where
  cn : IsCN V
  loc : IsLocalHom ev
  reg : RegAt X₁ z₁ ev

  yK : X₁.S.R →+* FractionRing V
  yK_eq : ∀ a : X₁.S.R, yK a = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a

  D : DegData V (maximalIdeal V)

  e₈ : (Fin 8 → X) ≃+ D.toPre.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  φ : A.A.left ⟶ X₁.ρ.P.A.left
  cart : IsGrpPullback A.A X₁.ρ.P.A (spMap yK) φ

  wl : LB.Iso A.L (X₁.ρ.P.L.pull φ)
  wl_gen : wl.IsGen
  equiv : ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) →
    ∃ E : EndU U.toUnifPre, E.aA.left ≫ φ = φ ≫ (act a).left ∧ ∀ mu, E.h (e₈ mu) = e₈ fun u => ∑ v, a' u v • mu v
  psi : ∀ mu, ∃ u : Vˣ, Formalism.L2.Pj.PsiCoord D.toPre (e₈ mu) (u * mono W t δ mu)

attribute [instance] UMem.grp UMem.comm

namespace UMem
variable {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)

def YY (a : X₁.S.Gam) (mu : Fin 8 → X) : Prop :=
  ∃ (p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
    (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), p.y = 𝔪.e₈ mu ∧
    QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x ∧
    x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left

def Over' (w₀ : W0 𝔪.U.toUnifPre) (g' : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b)
    (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm 𝔪.D.toPre (FractionRing V) k g'.b,
    (∀ z J, Good 𝔪.D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA 𝔪.A (FractionRing V) k) (s' : Fam 𝔪.D.toPre (FractionRing V) k) (v : FractionRing V),
      𝔪.U.ExpandsF (FractionRing V) k w₀ s s' → ValAt s x fr v → SumF (maximalIdeal V) (FractionRing V) (coef s' g' wk) v

def Terms (x₀ : X₁.S.Gam) {C : Type} (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) : Prop :=
  ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
    (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
    (w : ∀ c, Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
    (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧
    (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ w₀.IsGen ∧
    𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s ∧
    (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
      𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) ∧
    ∀ mu c, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ = coef s (g' c) (w c) (𝔪.e₈ mu)

end UMem

def IsGeo (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) : Prop :=
  X₁.M.Div X₁.S.th x₀ z₁ ∧ Set.range lab = X₁.S.HH X₁.M z₁ ∧
    ∀ y, ∃ 𝔪 : UMem X₁ z₁ act (Φ.V y) (Φ.ev y) (Φ.X y) (Φ.t y) (Φ.δ y), 𝔪.Terms x₀ lab (Φ.term y)

section
variable {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)

include 𝔪 in

theorem UMem.mono_ne_zero (mu : Fin 8 → X) : mono W t δ mu ≠ 0 :=
  let ⟨_, h⟩ := 𝔪.psi mu
  right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord h)

include 𝔪 in

theorem UMem.mono_mem {mu : Fin 8 → X} (h : mu ≠ 0) : mono W t δ mu ∈ maximalIdeal V := by
  haveI := 𝔪.cn.2.2.2
  obtain ⟨u, hu⟩ := 𝔪.psi mu
  obtain ⟨r, hr, -, hm, -⟩ := (PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hr hu
  have : (u : V) * mono W t δ mu ∈ maximalIdeal V := hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this

end

end Sep

end GlobalTheory.Poinc
