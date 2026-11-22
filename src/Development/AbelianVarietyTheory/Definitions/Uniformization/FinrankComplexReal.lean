import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.UU
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

@[simp] theorem sec_mk (s : LB.Sec N) : (mk p s).sec = s := rfl
@[simp] theorem mk_sec (s : SecMod p N) : mk p s.sec = s := rfl

@[simp] theorem add_f (s t : SecMod p N) (j : N.ι) : (s + t).sec.f j = s.sec.f j + t.sec.f j := rfl

@[simp] theorem neg_f (s : SecMod p N) (j : N.ι) : (-s).sec.f j = - s.sec.f j := rfl

@[simp] theorem smul_f (c : F) (s : SecMod p N) (j : N.ι) :
    (c • s).sec.f j = resTop _ (scal p c) * s.sec.f j := rfl

@[simp] theorem zero_f (j : N.ι) : (0 : SecMod p N).sec.f j = 0 := rfl

@[ext] theorem ext {s t : SecMod p N} (h : ∀ j, s.sec.f j = t.sec.f j) : s = t :=
  DVR.SecOps.sec_ext h

theorem eq_zero_iff (s : SecMod p N) : s = 0 ↔ ∀ j, s.sec.f j = 0 :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩

@[simp] theorem sub_f (s t : SecMod p N) (j : N.ι) : (s - t).sec.f j = s.sec.f j - t.sec.f j := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_f, neg_f]

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem sval_add (s t : SecMod p (LB.LinComb L φ ε)) :
    sval (s + t).sec r z J = sval s.sec r z J + sval t.sec r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

theorem sval_smul (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    sval (c • s).sec r z J = gs r z ⊤ (scal p c) * sval s.sec r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans
    (congrArg (· * sval s.sec r z J) (gs_res r z le_top (hJ.mem φ r) _))

end Val

variable (p) in

def ofFun (a : Γ(Y, ⊤)) : SecMod p (Inh.trivLB Y) :=
  mk p ⟨fun _ => a, fun _ _ => by erw [Units.val_one, _root_.one_mul]; rfl⟩

@[simp] theorem ofFun_f (a : Γ(Y, ⊤)) (j) : (ofFun p a).sec.f j = a := rfl

end SecMod
end GlobalTheory.UU
end
