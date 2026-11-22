import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwFam

variable {R : Type} [CommRing R] [IsDomain R]

def tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) : Fin 5 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left, (toUnit D.P.A ≫ D.c β).left,
    (toUnit D.P.A ≫ η[D.P.A]).left, a.left]

def tε (n j : ℤ) : Fin 5 → ℤ := ![n - 1, 1, -1, 1, j]

abbrev SecT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (tφ D a β) (tε n j))

def Van (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval s (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J = 0

def Small (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) : Prop :=
  ∀ e : ℕ, {i | ¬ Van I (s i) e}.Finite

def dφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (mu β β' : D.X) :
    Fin 5 ⊕ Fin 5 → ((DegPre.BF D (FractionRing R)).left ⟶ D.P.A.left) :=
  Sum.elim (fun k => (DegPre.prB D (FractionRing R)).left ≫ tφ D a β' k)
    (fun k => (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ tφ D a β k)

def dε (n j : ℤ) : Fin 5 ⊕ Fin 5 → ℤ := Sum.elim (tε n j) (fun k => - tε n j k)

def IsFac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) (n j : ℤ) (mu β β' : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) : Prop :=
  u.IsGen ∧ ∀ (z : (TF (R := R) (FractionRing R)).left) (J), Good D.P.L z J →
    val u (DegPre.zF D (FractionRing R)).left z J =
      val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)

def TRel {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h : D.X →+ D.X) {n j : ℤ} (mu : D.X) {β β' : D.X}
    (s : SecT D a n j β) (s' : SecT D a n j β') : Prop :=
  ∀ u, IsFac D a h n j mu β β' u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J),
    Good D.P.L z J → sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J =
      sval s (x ≫ (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left) z J * (val u x z J).val

def shift {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (mu : X) : X := n • mu + j • h' (h mu)

def TFE {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h h' : D.X →+ D.X) {n j : ℤ} (f : ∀ β, SecT D a n j β) : Prop :=
  ∀ mu β, TRel h mu (f β) (f (β + shift h h' n j mu))

open Classical in

def IsSum (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (F : ∀ δ, SecT D a n j δ) : Prop :=
  ∀ (e : ℕ) (S : Finset Ix), (∀ i ∉ S, Van I (s i) e) → ∀ (δ : D.X) (Z : Scheme.{0})
    (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval (F δ) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
        ∑ i ∈ S.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J

def IsProdT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j n' j' n'' j'' : ℤ} {β β' : D.X} (f : SecT D a n j β)
    (g : SecT D a n' j' β') (p : SecT D a n'' j'' (β + β')) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval p x z J = sval f x z J * sval g x z J *
      (val D.cub.t (x ≫ (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left) z J).val

abbrev IotaLB (D : DegPre R) (a : D.P.A ⟶ D.P.A) (α δ : D.X) : LB D.P.A.left :=
  LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)) (Sum.elim Oε Oinvε)

def IsIota {D : DegPre R} {a : D.P.A ⟶ D.P.A} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J → val u (r ≫ eSec D.P.A) z J = 1

def IsPullT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {k : ℕ} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) (f : D.SecB k α)
    (s : SecT D a 0 k δ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval s x z J = sval f (x ≫ a.left) z J * (val u x z J).val

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev SecE (U : UnifPre I D A G) {e : ℕ} (b : thickObj R I e G ⟶ thickObj R I e G) (n j : ℤ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 2) ![(fstG I e G).left, b.left ≫ (fstG I e G).left] ![n, j])

def evalE (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ G.left) → U.LG.L.ι) : Z.presheaf.stalk z :=
  (DVR.wv U e x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (fstG I e G).left)) ^ n *
    DVR.wv U e (x ≫ b.left) z (J (x ≫ b.left ≫ (U.gt e).pG.left)) (J' (x ≫ b.left ≫ (fstG I e G).left)) ^ j).val *
    sval τ x z J'

def TExp (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {a : D.toPre.P.A ⟶ D.toPre.P.A}
    {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) : Prop :=
  ∀ S : Finset Ix, (∀ i ∉ S, Van I (s i) e) → ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
    Good D.toPre.P.L z J → Good U.LG.L z J' → evalE U τ x z J J' =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val

def zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : SecT D a n j β := ⟨fun _ => 0, fun _ _ => by simp⟩

theorem sval_zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) {Z : Scheme.{0}} (x : Z ⟶ D.P.A.left) (z : Z) (J)
    (hJ : Good D.P.L z J) : sval (zeroT D a n j β) x z J = 0 := DVR.gs_zero x z _ (hJ.mem _ x)

namespace Witness

end Witness

end GlobalTheory.TwFam
