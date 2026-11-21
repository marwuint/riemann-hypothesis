import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEndPullEndPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.ThetaLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

namespace Thg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}

section Ring

variable (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)

def fn (R : Type) [CommRing R] : R ≃+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

def torsSub (n : ℕ) : Subgroup (Over.mk x ⟶ t.G) where
  carrier := {a | a ^ n = 1 ∧ (n = 0 → a = 1)}
  one_mem' := ⟨one_pow n, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [mul_pow, ha.1, hb.1, _root_.mul_one], fun h => by rw [ha.2 h, hb.2 h, _root_.mul_one]⟩
  inv_mem' := fun {a} ha => ⟨by rw [inv_pow, ha.1, inv_one], fun h => by rw [ha.2 h, inv_one]⟩

def thSub (n : ℕ) : Subgroup (ThetaGrp t.G t.PP.L n (Over.mk x)) := (torsSub t x n).comap (ptHom (n : ℤ) (Over.mk x) t.PP)

theorem mem_thSub {n : ℕ} (θ : ThetaGrp t.G t.PP.L n (Over.mk x)) : θ ∈ thSub t x n ↔ θ.pt ∈ torsSub t x n := Iff.rfl

def Sec (k : ℤ) : Type := SecM t.G t.PP.L k (Over.mk x)

instance (k : ℤ) : AddCommGroup (Sec t x k) := inferInstanceAs (AddCommGroup (SecM t.G t.PP.L k (Over.mk x)))

instance (k : ℤ) : Module R (Sec t x k) :=
  Module.compHom (SecM t.G t.PP.L k (Over.mk x)) (show R →+* Γ((Over.mk x).left, ⊤) from (fn R).toRingHom)

variable {t x}

def Sec.toM {k : ℤ} (s : Sec t x k) : SecM t.G t.PP.L k (Over.mk x) := s

def Sec.toSec {k : ℤ} (s : Sec t x k) : LB.Sec (LPow t.G t.PP.L k (Over.mk x)) := SecM.toSec t.G s.toM

def Sec.ofSec {k : ℤ} (s : LB.Sec (LPow t.G t.PP.L k (Over.mk x))) : Sec t x k := SecM.ofSec t.G s

def Sec.lin {k k' : ℤ} (f : SecM t.G t.PP.L k (Over.mk x) →ₗ[Γ((Over.mk x).left, ⊤)] SecM t.G t.PP.L k' (Over.mk x)) :
    Sec t x k →ₗ[R] Sec t x k' where
  toFun := f
  map_add' := f.map_add
  map_smul' c s := f.map_smul (show Γ((Over.mk x).left, ⊤) from fn R c) s

def ptMap {R' : Type} [CommRing R'] (f : R →+* R') {x' : Sp R' ⟶ X} (h : spMap f ≫ x = x') : Over.mk x' ⟶ Over.mk x :=
  Over.homMk (spMap f) h

def Sec.pull {R' : Type} [CommRing R'] (f : R →+* R') {x' : Sp R' ⟶ X} (h : spMap f ≫ x = x') (k : ℤ) :
    Sec t x k →ₛₗ[f] Sec t x' k where
  toFun := VVRank.pullM t.G t.PP.L k (ptMap f h)
  map_add' := map_add _
  map_smul' c s := ((VVRank.pullM t.G t.PP.L k (ptMap f h)).map_smulₛₗ (show Γ((Over.mk x).left, ⊤) from fn R c) s).trans
    (congrArg (fun a : Γ((Over.mk x').left, ⊤) => a • VVRank.pullM t.G t.PP.L k (ptMap f h) s)
      (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm)

def Sec.IsBasis {k : ℤ} (θ : Sec t x k) : Prop := ∀ s : Sec t x k, ∃! c : R, s = c • θ

theorem Sec.IsBasis.ne_zero [Nontrivial R] {k : ℤ} {θ : Sec t x k} (h : θ.IsBasis) : θ ≠ 0 := fun e =>
  zero_ne_one ((h θ).unique (by rw [zero_smul, e]) (one_smul _ _).symm)

variable (t x)

variable {t x}

variable (t)

variable (x)

variable {t x}

end Ring

end Thg

namespace At

end At

namespace Thg

end Thg

end GlobalTheory.LocM
