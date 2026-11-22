import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalFirstChernSurjective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad

namespace NModel

section GenIso

variable {O : Type} [CommRing O] [IsLocalRing O] (Z : NModel O)

@[ext] structure GenIso (L L' : LB Z.X) : Type where

  u : ∀ (i : L.ι) (j : L'.ι), Γ(Z.X, Z.gen ⊓ (L.U i ⊓ L'.U j))ˣ

  rel : ∀ (i i₁ : L.ι) (j j₁ : L'.ι),
    res (inf_le_left : Z.gen ⊓ (L.U i ⊓ L'.U j) ⊓ (L.U i₁ ⊓ L'.U j₁) ≤ _) (u i j) *
      res (inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right) (L'.g j j₁) =
    res (inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left) (L.g i i₁) *
      res (inf_le_inf_right _ inf_le_left) (u i₁ j₁)

namespace GenIso

variable {Z} {L L' L'' : LB Z.X} (φ : Z.GenIso L L')

theorem rel' (i i₁ : L.ι) (j j₁ : L'.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ (L.U i ⊓ L'.U j))
    (h₁ : W ≤ Z.gen ⊓ (L.U i₁ ⊓ L'.U j₁)) (hi : W ≤ L.U i ⊓ L.U i₁) (hj : W ≤ L'.U j ⊓ L'.U j₁) :
    res h (φ.u i j) * res hj (L'.g j j₁) = res hi (L.g i i₁) * res h₁ (φ.u i₁ j₁) := by
  have := congrArg (fun u => (res (le_inf h (h₁.trans inf_le_right)) u).val) (φ.rel i i₁ j j₁)
  refine Units.ext ?_
  simpa only [map_mul, Units.val_mul, val_res, resG_resG] using this

def pair (hL : L.IsLB) (hL' : L'.IsLB) : VPair Z :=
  .ofUnits (LB.div L L') (Semi.LB.isLB_div hL hL') (fun p => (φ.u p.1 p.2).val) (fun _ => Units.isUnit _) fun p q => by
    have := congrArg Units.val (eq_mul_inv_iff_mul_eq.2 (φ.rel p.1 q.1 p.2 q.2))
    rw [mul_right_comm] at this
    refine this.trans (congrArg (· * _) ?_)
    change _ = (res _ (res _ _ * (res _ _)⁻¹)).val
    rw [map_mul, map_inv]
    exact congrArg Units.val (congrArg₂ (fun a b => a * b⁻¹) (Semi.LB.res_res _ _ _) (Semi.LB.res_res _ _ _)).symm

def dual : Z.GenIso (CechPic.dual L) (CechPic.dual L') where
  u i j := (φ.u i j)⁻¹
  rel i i₁ j j₁ := by
    have := congrArg (·⁻¹) (φ.rel i i₁ j j₁)
    simp only [mul_inv, ← map_inv] at this
    exact this

def symm : Z.GenIso L' L where
  u j i := res (inf_le_inf_left _ (inf_comm _ _).le) (φ.u i j)⁻¹
  rel j j₁ i i₁ := by
    have h := φ.rel' i i₁ j j₁ (W := Z.gen ⊓ (L'.U j ⊓ L.U i) ⊓ (L'.U j₁ ⊓ L.U i₁))
      (inf_le_left.trans (inf_le_inf_left _ (inf_comm _ _).le))
      (inf_le_inf inf_le_left (inf_comm _ _).le)
      (inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right)
      (inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    have e (a b) {W W' : Z.X.Opens} (h₁ : W ≤ Z.gen ⊓ (L.U a ⊓ L'.U b)) (h₂ : W' ≤ W) :
        res h₂ (res h₁ (φ.u a b)⁻¹) = (res (h₂.trans h₁) (φ.u a b))⁻¹ :=
      (Units.ext (resG_resG _ _ _)).trans (map_inv _ _)
    rw [e, e, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h.symm

def ofGlobal (w : LB.Iso L' L) (hw : w.IsGen) : Z.GenIso L L' where
  u i j := res inf_le_right (w.s (i, j))
  rel i i₁ j j₁ := by
    have h : res _ (w.s (i, j)) = res _ _ * (res _ _)⁻¹ * res _ (w.s (i₁, j₁)) := hw (i, j) (i₁, j₁)
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at h
    have := congrArg (res (inf_le_inf_right (L.U i₁ ⊓ L'.U j₁) (inf_le_right : Z.gen ⊓ (L.U i ⊓ L'.U j) ≤ _))) h
    rw [map_mul, map_mul] at this
    exact (congrArg₂ (· * ·) ((Semi.LB.res_res _ _ _).trans (Semi.LB.res_res _ _ _).symm)
      (Semi.LB.res_res _ _ _).symm).trans (this.trans (congrArg₂ (· * ·) (Semi.LB.res_res _ _ _)
        ((Semi.LB.res_res _ _ _).trans (Semi.LB.res_res _ _ _).symm)))

end GenIso

end GenIso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

namespace GenIso

variable {L L' L'' : LB Z.X} (φ : Z.GenIso L L') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)

def smul (g : O) (hg : g ≠ 0) : Z.GenIso L L where
  u i j := (Z.isUnit_const hg inf_le_left).unit * res inf_le_right (L.g i j)
  rel i i₁ j j₁ := by
    refine unit_ext fun y hy => ?_
    have e (a b : L.ι) (h : y ∈ Z.gen ⊓ (L.U a ⊓ L.U b)) :
        gm (𝟙 Z.X) y _ (Z.isUnit_const hg (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _)).unit =
          gm (𝟙 Z.X) y _ (Z.isUnit_const hg le_rfl).unit := by
      rw [← gm_res (𝟙 Z.X) y (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _) h]
      exact congrArg _ (Units.ext (resG_resG _ _ _).symm)
    have h₁ : y ∈ Z.gen ⊓ (L.U i₁ ⊓ L.U j₁) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 Z.X) y _ hy, gm_res (𝟙 Z.X) y _ hy.1, gm_res (𝟙 Z.X) y _ h₁, e _ _ hy.1, e _ _ h₁]
    rw [mul_assoc, gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.1.2.2 hy.2.2, mul_left_comm,
      gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.2.1 hy.2.2]

def div : Z.VDivZ := (φ.pair hL hL').cls

@[simp] theorem vCls_div : Z.vCls (φ.div hL hL') = cls L hL - cls L' hL' := (vCls_cls _).trans (cls_div _ _ _)

theorem div_eq_add (φ' : Z.GenIso L' L'') (φ'' : Z.GenIso L L'')
    (h : ∀ i j k, res (inf_le_inf_left _ (inf_le_inf_right _ inf_le_left) :
        Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L''.U k) ≤ _) (φ''.u i k) =
      res (inf_le_inf_left _ inf_le_left) (φ.u i j) *
        res (inf_le_inf_left _ (inf_le_inf_right _ inf_le_right)) (φ'.u j k)) :
    φ''.div hL hL'' = φ.div hL hL' + φ'.div hL' hL'' := by
  refine VPair.isSum_iff.1 fun a b c => ?_
  obtain ⟨i, j⟩ := a
  obtain ⟨j₁, k⟩ := b
  obtain ⟨i₁, k₁⟩ := c
  let V := L.U i ⊓ L'.U j ⊓ (L'.U j₁ ⊓ L''.U k) ⊓ (L.U i₁ ⊓ L''.U k₁)
  have hi : V ≤ L.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : V ≤ L'.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hj₁ : V ≤ L'.U j₁ := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hk : V ≤ L''.U k := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hi₁ : V ≤ L.U i₁ := inf_le_right.trans inf_le_left
  have hk₁ : V ≤ L''.U k₁ := inf_le_right.trans inf_le_right
  refine ⟨res (le_inf hi₁ hi) (L.g i₁ i) * res (le_inf hj hj₁) (L'.g j j₁) * (res (le_inf hk₁ hk) (L''.g k₁ k))⁻¹, ?_⟩
  have e (W W' W'' : Z.X.Opens) (h₁ : W' ≤ W) (h₂ : W'' ≤ W') (u : Γ(Z.X, W)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := Units.ext (resG_resG _ _ _)
  have h₁ := φ''.rel' i₁ i k₁ k (W := Z.gen ⊓ V) (inf_le_inf_left _ (le_inf hi₁ hk₁))
    (inf_le_inf_left _ (le_inf hi hk)) (inf_le_right.trans (le_inf hi₁ hi)) (inf_le_right.trans (le_inf hk₁ hk))
  have h₂ := φ.rel' i i j j₁ (W := Z.gen ⊓ V) (inf_le_inf_left _ (le_inf hi hj))
    (inf_le_inf_left _ (le_inf hi hj₁)) (inf_le_right.trans (le_inf hi hi)) (inf_le_right.trans (le_inf hj hj₁))
  have h₃ := congrArg (res (inf_le_inf_left Z.gen (le_inf (le_inf hi hj₁) hk))) (h i j₁ k)
  have h₄ := congrArg (res ((inf_le_right : Z.gen ⊓ V ≤ V).trans hi)) (hL.g_self i)
  simp only [map_mul, e, map_one] at h₃ h₄
  rw [h₄, one_mul] at h₂
  rw [h₃, ← h₂, ← eq_mul_inv_iff_mul_eq] at h₁
  refine (congrArg Units.val h₁).trans ?_
  change _ = (res (inf_le_right : Z.gen ⊓ V ≤ V) _ * (res _ (φ.u i j) * res _ (φ'.u j₁ k))).val
  refine congrArg Units.val ?_
  simp only [map_mul, map_inv, e]
  ac_rfl

@[simp] theorem div_ofGlobal (w : LB.Iso L' L) (hw : w.IsGen) : (ofGlobal w hw : Z.GenIso L L').div hL hL' = 0 := by
  rw [← VPair.cls_zero]
  refine (VPair.cls_eq_iff.2 (VPair.isIsom_of_units (fun p _ => res inf_le_left (w.s p)) fun p q => ?_)).symm
  change resG _ _ (resG _ _ _) = resG _ _ (resG _ _ _) * resG _ _ 1
  rw [map_one, mul_one]
  exact (resG_resG _ _ _).trans (resG_resG _ _ _).symm

@[simp] theorem div_smul (g : O) (hg : g ≠ 0) : (smul hL g hg).div hL hL = Z.div g hg := by
  refine (VPair.cls_eq_iff.2 (VPair.isIsom_of_units
    (P' := (smul hL g hg).pair hL hL) (fun p _ => res inf_le_left (L.g p.1 p.2)) fun p q => ?_)).symm
  change resG _ _ (resG _ _ _ * resG _ _ _) = resG _ _ (resG _ _ _) * resG _ _ (resG _ _ _)
  rw [map_mul, mul_comm]
  exact congrArg₂ (· * ·) ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)
    ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)

@[simp] theorem div_symm : φ.symm.div hL' hL = -φ.div hL hL' := by
  refine eq_neg_of_add_eq_zero_right ((φ.div_eq_add hL hL' hL φ.symm (ofGlobal (idIso L) (idIso_isGen hL))
    fun i j k => ?_).symm.trans (div_ofGlobal _ _ _ _))
  have h₁ := φ.rel' i k j j (W := Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L.U k)) (inf_le_inf_left _ inf_le_left)
    (inf_le_inf_left _ (le_inf inf_le_right (inf_le_left.trans inf_le_right)))
    (inf_le_right.trans (inf_le_inf_right _ inf_le_left))
    (inf_le_right.trans (inf_le_left.trans (le_inf inf_le_right inf_le_right)))
  have h₂ := congrArg (res ((inf_le_right : Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L.U k) ≤ _).trans
    (inf_le_left.trans inf_le_right))) (hL'.g_self j)
  rw [Semi.LB.res_res, map_one] at h₂
  rw [h₂, mul_one, ← mul_inv_eq_iff_eq_mul, ← map_inv] at h₁
  exact (Semi.LB.res_res _ _ _).trans (h₁.symm.trans (congrArg _ (Semi.LB.res_res _ _ _).symm))

@[simp] theorem div_dual : φ.dual.div (isLB_dual hL) (isLB_dual hL') = -φ.div hL hL' := by
  refine eq_neg_of_add_eq_zero_right ((VPair.isSum_iff.1 fun a b c => ?_).symm.trans (VPair.cls_zero Z))
  obtain ⟨i, j⟩ := a
  obtain ⟨i₁, j₁⟩ := b
  let V := L.U i ⊓ L'.U j ⊓ (L.U i₁ ⊓ L'.U j₁) ⊓ ⊤
  have hi : V ≤ L.U i ⊓ L.U i₁ := inf_le_left.trans (inf_le_inf inf_le_left inf_le_left)
  have hj : V ≤ L'.U j ⊓ L'.U j₁ := inf_le_left.trans (inf_le_inf inf_le_right inf_le_right)
  refine ⟨res hj (L'.g j j₁) * (res hi (L.g i i₁))⁻¹, ?_⟩
  have h₁ := φ.rel' i i₁ j j₁ (W := Z.gen ⊓ V) (inf_le_inf_left _ (inf_le_left.trans inf_le_left))
    (inf_le_inf_left _ (inf_le_left.trans inf_le_right)) (inf_le_right.trans hi) (inf_le_right.trans hj)
  refine (map_one _).trans ?_
  change (1 : Γ(Z.X, Z.gen ⊓ V)ˣ).val =
    (res (inf_le_right : Z.gen ⊓ V ≤ V) _ * (res _ (φ.u i j) * res _ (φ.u i₁ j₁)⁻¹)).val
  refine congrArg Units.val ?_
  simp only [map_mul, map_inv, Semi.LB.res_res]
  rw [mul_mul_mul_comm, mul_comm (res _ (L'.g j j₁)), h₁, ← mul_inv, mul_inv_cancel]

end GenIso

variable (Z)

abbrev VDivQ : Type := ℚ ⊗[ℤ] Z.VDivZ

variable {Z} in

def toQ : Z.VDivZ →+ Z.VDivQ := (TensorProduct.mk ℤ ℚ Z.VDivZ 1).toAddMonoidHom

def cDQ : Z.VDivQ →ₗ[ℚ] PicSym Z.X := LinearMap.liftBaseChange ℚ (firstChernPic.comp Z.vCls).toIntLinearMap

def capDeg_vp (p d : ℕ) : Z.VDivQ →ₗ[ℚ] PicSym Z.X →ₗ[ℚ] ℚ :=
  (ramIdx O p : ℚ)⁻¹ • LinearMap.liftBaseChange ℚ (Z.vDeg d).toIntLinearMap

variable {Z}

@[simp] theorem cDQ_toQ (D : Z.VDivZ) : Z.cDQ (toQ D) = firstChernPic (Z.vCls D) := by simp [cDQ, toQ]

def vResQ (C : Z.Comp) : Z.VDivQ →ₗ[ℚ] (Z.comp C).VDivQ := (Z.vRes C).toIntLinearMap.baseChange ℚ

@[simp] theorem vResQ_toQ (C : Z.Comp) (D : Z.VDivZ) : vResQ C (toQ D) = Model.toQ (Z.vRes C D) := rfl

section Theory

variable (Z) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def divP : Z.VDivZ := Z.div p (natCast_ne_zero O p)

set_option linter.overlappingInstances false in

@[reducible] def toITh [CharP (ResidueField O) p] (d : ℕ) : Formalism.BasicNotions.DV.ITh where
  LB := FinLB Z.X
  Ch := PicSym Z.X
  c1 := FinLB.c1
  VDiv := Z.VDivQ
  cD := Z.cDQ
  capDeg := Z.capDeg_vp p d
  divP := toQ (Z.divP p)
  cD_divP := by simp [divP]
  dim := d + 1

end Theory

variable (Z) in

def vdiv (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : Z.VDivQ := toQ (u.div L.isLB L'.isLB)

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : L'.c1 = L.c1 - Z.cDQ (Z.vdiv L L' u) := by
  rw [vdiv, cDQ_toQ, GenIso.vCls_div, map_sub]
  exact (sub_sub_cancel _ _).symm

end NModel

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Model O} {f : B'.X ⟶ B.X} [IsIso f]
  (hf : f ≫ B.str = B'.str)

variable (f) in
include f in

theorem relDim_eq_of_isIso : B'.relDim = B.relDim := by
  refine Model.relDim_eq_iff.2 (Eq.trans ?_ B.dim_eq)
  rw [← topologicalKrullDim_eq_of_isEmbedding f.isOpenEmbedding.isEmbedding f.surjective.range_eq,
    topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id]

end Iso

namespace NModel

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

def sigma {ι : Type} [Finite ι] (B : ι → Model O) [∀ i, GlobalTheory.IsNormalScheme (B i).X] : NModel O where
  X := ∐ fun i => (B i).X
  str := Sigma.desc fun i => (B i).str
  isProjOver := ProjSpace.isProjOver_sigmaDesc _ fun i => (B i).isProjOver
  flat := IsZariskiLocalAtSource.sigmaDesc fun i => (B i).flat

section Example

variable (O) (n N : ℕ) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def copies : NModel O :=
  haveI := Model.isNormalScheme_projSpace O N
  sigma fun _ : Fin n => Model.projSpace O N

end Example

end NModel

section Mdl

open NumberField GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

@[reducible] def nmodel (Z : Mdl Y i₀) : NModel (Z.i.c.V W) where
  X := Z.X
  str := Z.s
  normal := Z.normal
  isProjOver := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  flat := Z.flat

theorem natCast_mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp.ne_zero
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isDiscreteValuationRing_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) :=
  haveI := c.fin
  haveI : NumberField c.F := {}
  (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero
    (natCast_mem_nonunits_V c hp hW)).1

theorem charP_residueField_of_mem_nonunits {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    CharP (ResidueField (c.V W)) p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  rw [← map_natCast (residue (c.V W)), residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact_mod_cast natCast_mem_nonunits_V c hp hW

abbrev GenIso (Z : Mdl Y i₀) (L L' : FinLB Z.X) : Type := (nmodel Z).GenIso L.lb L'.lb

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (d : ℕ)

@[reducible] def ithOf : Formalism.BasicNotions.DV.ITh :=
  haveI := Fact.mk hp
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits Z.i.c hp hW
  (nmodel Z).toITh p d

variable {Z}

def vdiv (L L' : FinLB Z.X) (u : GenIso Z L L') : (ithOf hp hW Z d).VDiv :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  (nmodel Z).vdiv L L' u

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : GenIso Z L L') :
    (ithOf hp hW Z d).c1 L' = (ithOf hp hW Z d).c1 L - (ithOf hp hW Z d).cD (vdiv hp hW d L L' u) :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  NModel.firstChern_eq_sub_divisor (Z := nmodel Z) L L' u

def fpairOf {r : ℕ} (x x' : Fin r → FinLB Z.X) (u : ∀ i, GenIso Z (x i) (x' i)) :
    Formalism.BasicNotions.DV.FPair (ithOf hp hW Z d) r :=
  ⟨x, x', fun i => vdiv hp hW d _ _ (u i), fun i => firstChern_eq_sub_divisor hp hW d _ _ (u i)⟩

include hp hW

theorem gen_eq_basicOpen : (nmodel Z).gen = Z.X.basicOpen (p : Γ(Z.X, ⊤)) := by
  have := Fact.mk hp
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have := charP_residueField_of_mem_nonunits Z.i.c hp hW
  rw [(nmodel Z).gen_eq_basicOpen (natCast_ne_zero _ p) (natCast_mem_maximalIdeal _ p), map_natCast]

theorem mem_gen_iff_inQ {x : Z.X} : x ∈ (nmodel Z).gen ↔ Z.inQ x := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have h (g : Z.i.c.V W) : (Z.X.evaluation ⊤ x trivial).hom ((nmodel Z).const g) ≠ 0 ↔
      x ∈ Z.X.basicOpen ((nmodel Z).const g) := Z.X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) x trivial _
  refine ⟨fun hx => charZero_of_inj_zero fun n hn => by_contra fun h0 => ?_, fun hx => ?_⟩
  · exact (h n).2 ((nmodel Z).gen_le_basicOpen (Nat.cast_ne_zero.2 h0) hx) (by simpa using hn)
  · have : CharZero (Z.X.residueField x) := hx
    rw [gen_eq_basicOpen hp hW, ← map_natCast (nmodel Z).const, ← h]
    simpa using hp.ne_zero

theorem chart_le_gen (a : Fin Z.m) : (Z.U a).1 ≤ (nmodel Z).gen := by
  rw [gen_eq_basicOpen hp hW]
  refine le_basicOpen_of_isUnit le_top ?_
  rw [map_natCast, ← map_natCast (Z.alg a)]
  exact (Ne.isUnit (Nat.cast_ne_zero.2 hp.ne_zero)).map _

end Mdl

end GlobalTheory.ShFam.Pad
