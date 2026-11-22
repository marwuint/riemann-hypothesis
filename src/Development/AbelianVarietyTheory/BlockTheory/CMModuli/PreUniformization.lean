import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization

variable {R : Type} [CommRing R] [IsDomain R]

abbrev Red (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R)) :=
  (Over.map (thick R I e)).obj (thickObj R I e G)

def isoV {X₁ X₂ Y Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (r : Z ⟶ Y) (z : Z) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))

abbrev pt3 (I : Ideal R) (e : ℕ) {G H : Over (Spec (CommRingCat.of R))} (p : Red I e G ⟶ H)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y u : T ⟶ thickObj R I e G) :
    T.left ⟶ (H ⊗ H ⊗ H).left :=
  (lift ((Over.map (thick R I e)).map x ≫ p)
    (lift ((Over.map (thick R I e)).map y ≫ p) ((Over.map (thick R I e)).map u ≫ p))).left

structure PreUnif (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom

  gen : (Over.pullback (jK R)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L.L z J →
    val sym (r ≫ eSec G) z J = 1
  extendsL : ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK R))), w.IsGen

  j : ∀ e : ℕ, GtCoord I D e G
  j_base : ∀ e : ℕ, thickMap R I e G ≫ (j (e + 1)).pG.left = (j e).pG.left
  j_coord : ∀ (e : ℕ) (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
    val ((j (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((j e).t χ) r z J

  ph : ∀ e : ℕ, LB.Iso (L.L.pull (fstG I e G).left) (D.P.L.pull (j e).pG.left)
  ph_gen : ∀ e, (ph e).IsGen
  ph_rig : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    val (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (r ≫ thick R I e) z JM =
      isoV (ph e) (r ≫ eSec (thickObj R I e G)) z JL JM *
        val (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig (r ≫ thick R I e) z JL
  ph_even : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    val D.sym (r ≫ (j e).pG.left) z JM * isoV (ph e) r z JL JM =
      isoV (ph e) (r ≫ (ι[thickObj R I e G]).left) z JL JM * val sym (r ≫ (fstG I e G).left) z JL
  ph_cub : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y u : T ⟶ thickObj R I e G)
    (z : T.left) (JL) (JM), Good L.L z JL → Good D.P.L z JM →
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (pt3 I e (j e).pG x y u) z JM *
        isoV (ph e) (x * y).left z JL JM * isoV (ph e) (x * u).left z JL JM * isoV (ph e) (y * u).left z JL JM *
        isoV (ph e) (1 : T ⟶ thickObj R I e G).left z JL JM =
      isoV (ph e) (x * y * u).left z JL JM * isoV (ph e) x.left z JL JM * isoV (ph e) y.left z JL JM *
        isoV (ph e) u.left z JL JM *
        val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) cub.t (pt3 I e (fstG I e G) x y u) z JL
  ph_compat : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    isoV (ph (e + 1)) (r ≫ thickMap R I e G) z JL JM = isoV (ph e) r z JL JM

def compφ (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (α : D.X) :
    Fin 4 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (snd T D.P.A * (toUnit _ ≫ D.c α)).left, (toUnit (T ⊗ D.P.A) ≫ D.c α).left,
    (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left]

abbrev SecB (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (compφ D T α) ![(k : ℤ) - 1, 1, -1, 1])

abbrev RawFam (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  ∀ α : D.X, SecB D (TF (R := R) F) k α

namespace PreUnif

end PreUnif

section Ph

variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

def Ph (k : ℕ) (y : D.X) (g : GtPtF D F)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (s s' : RawFam D F k) : Prop :=
  g.b ^ k = toUnit _ ≫ D.c y ∧ w.IsGen ∧
  ∀ (α : D.X) (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ TF (R := R) F) (x : Z ⟶ D.P.A) (z : Z.left)
    (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval (s' (α + y)) (lift r x).left z J =
      (cubN (cubV D.cub z J) k (toUnit Z ≫ D.c α) (r ≫ g.b) x * (cubV D.cub z J (toUnit Z ≫ D.c α) x (r ≫ g.b))⁻¹ *
        val (g.s α) r.left z J * val w r.left z J).val * sval (s α) (lift r (x * (r ≫ g.b))).left z J

theorem Ph.unique {k : ℕ} {y : D.X} {g : GtPtF D F} {w} {s s₁ s₂ : RawFam D F k} (h₁ : Ph D F k y g w s s₁)
    (h₂ : Ph D F k y g w s s₂) : s₁ = s₂ := by
  funext β
  obtain ⟨α, rfl⟩ : ∃ α, β = α + y := ⟨β - y, (sub_add_cancel _ _).symm⟩
  have e : (s₁ (α + y)).f = (s₂ (α + y)).f := funext fun j => sec_ext_val D.P.isLB (fun z J hJ => by
    have a := (h₁.2.2 α _ (fst _ _) (snd _ _) z J hJ).trans (h₂.2.2 α _ (fst _ _) (snd _ _) z J hJ).symm
    rwa [lift_fst_snd] at a) j
  cases hs₁ : s₁ (α + y); cases hs₂ : s₂ (α + y)
  rw [hs₁, hs₂] at e
  congr

end Ph

end GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
end
