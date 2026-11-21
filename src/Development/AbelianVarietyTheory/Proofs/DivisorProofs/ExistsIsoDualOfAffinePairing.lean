import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self homOfLinear fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB

namespace GlobalTheory.AffinePairingGlue

variable {T : Scheme.{0}} {H : T.Modules}

theorem exists_affine_le {V : T.Opens} {x : T} (hx : x ∈ V) :
    ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V := by
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  exact ⟨W, hW, hxW, hWV⟩

theorem le_iSup_affine (V : T.Opens) :
    V ≤ ⨆ W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V}, W.1 := fun x hx => by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_affine_le hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWV⟩, hxW⟩

theorem fun_ext_affine {V : T.Opens} {a a' : Γ(T, V)}
    (e : ∀ (W : T.Opens) (_ : IsAffineOpen W) (h : W ≤ V), resG T h a = resG T h a') : a = a' :=
  fun_ext_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1) (fun W => W.2.2)
    (le_iSup_affine V) fun W => e W.1 W.2.1 W.2.2

variable (b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V)))
  (hb : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s t : Γ(H, V)), b V' hV' (resM H h s) (resM H h t) = resG T h (b V hV s t))

include hb in

theorem exists_glued (V : T.Opens) (s t : Γ(H, V)) : ∃ a : Γ(T, V),
    ∀ (W : T.Opens) (hW : IsAffineOpen W) (h : W ≤ V),
      resG T h a = b W hW (resM H h s) (resM H h t) := by
  obtain ⟨a, ha⟩ := exists_fun_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1)
    (fun W => W.2.2) (le_iSup_affine V)
    (fun W => b W.1 W.2.1 (resM H W.2.2 s) (resM H W.2.2 t)) fun k l =>
      fun_ext_affine fun W hW h => by
        rw [resG_resG, resG_resG, ← hb _ _ k.2.1 hW, ← hb _ _ l.2.1 hW]
        simp only [resM_resM]
  exact ⟨a, fun W hW h => ha ⟨W, hW, h⟩⟩

def glued (V : T.Opens) (s t : Γ(H, V)) : Γ(T, V) := (exists_glued b hb V s t).choose

theorem resG_glued {V W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ V) (s t : Γ(H, V)) :
    resG T h (glued b hb V s t) = b W hW (resM H h s) (resM H h t) :=
  (exists_glued b hb V s t).choose_spec W hW h

theorem glued_res {V W : T.Opens} (h : W ≤ V) (s t : Γ(H, V)) :
    glued b hb W (resM H h s) (resM H h t) = resG T h (glued b hb V s t) :=
  fun_ext_affine fun U hU h' => by
    rw [resG_resG, resG_glued b hb hU, resG_glued b hb hU, resM_resM, resM_resM]

def gluedBilin (V : T.Opens) : Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V) :=
  LinearMap.mk₂ Γ(T, V) (glued b hb V)
    (fun s s' t => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU, LinearMap.add_apply])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul,
        LinearMap.smul_apply])
    (fun s t t' => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul])

def toDual : H ⟶ dual H :=
  homOfLinear (fun V =>
    { toFun s := dualMk (fun W h => gluedBilin b hb W (resM H h s))
        fun W W' h h' t => by
          change glued b hb W' _ _ = resG T h' (glued b hb W _ _)
          rw [← glued_res, resM_resM]
      map_add' := fun s t => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (s + t)) u = _
        rw [map_add, map_add]; rfl
      map_smul' := fun a s => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (a • s)) u = _
        rw [resM_smul, map_smul]; rfl })
    fun h s => dual_ext fun W h' u =>
      congrArg (fun z => glued b hb W z u) (resM_resM h h' s)

theorem dualApp_toDual {V W : T.Opens} (h : W ≤ V) (s : Γ(H, V)) (t : Γ(H, W)) :
    dualApp ((toDual b hb).app V s) h t = glued b hb W (resM H h s) t := rfl

end GlobalTheory.AffinePairingGlue
