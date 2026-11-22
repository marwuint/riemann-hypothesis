import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

namespace Var

variable {F : Type} [Field F] (Y : Var F)

instance isNoetherian_X : AlgebraicGeometry.IsNoetherian Y.X :=
  isNoetherian_of_isProjOver Y.isProjOver

def sheaf (Δ : Y.Dv) : Y.X.Modules := twist (structureModule Y.X) (Y.lb Δ)

instance isFiniteQC_sheaf (Δ : Y.Dv) : IsFiniteQC (Y.sheaf Δ) :=
  Twist.isFiniteQC_twist (isLB_toLB Δ)

abbrev H (i : ℕ) (Δ : Y.Dv) : Type := coh (Y.sheaf Δ) i

def hdim (i : ℕ) (Δ : Y.Dv) : ℕ := GlobalTheory.hdim F (Y.sheaf Δ) i

def chi (Δ : Y.Dv) : ℤ := GlobalTheory.chi F (Y.sheaf Δ)

instance finite_H (i : ℕ) (Δ : Y.Dv) : FiniteDimensional F (Y.H i Δ) :=
  finite_coh_of_isProjOver Y.algebraMap_Γ _ Y.isProjOver i

theorem hdim_def (i : ℕ) (Δ : Y.Dv) : Y.hdim i Δ = Module.finrank F (Y.H i Δ) := rfl

def inter (Δ : Fin Y.dim → Y.Dv) : ℤ := interNum F (structureModule Y.X) fun i => Y.lb (Δ i)

theorem inter_eq_multiDiff (Δ : Fin Y.dim → Y.Dv) : Y.inter Δ = multiDiff Δ Y.chi 0 := by
  have e := congrFun (multiDiff_comap toPic Δ (chiPic F (structureModule Y.X))) 0
  rw [Function.comp_apply, map_zero] at e
  exact (interNum_eq_multiDiff F _ fun i => isLB_toLB (Δ i)).trans e.symm

variable {Y} in

theorem inter_eq_of_toPic_eq {Δ : Fin Y.dim → Y.Dv} {L : Fin Y.dim → LB Y.X}
    (hL : ∀ i, (L i).IsLB) (e : ∀ i, toPic (Δ i) = cls (L i) (hL i)) :
    Y.inter Δ = interNum F (structureModule Y.X) L :=
  interNum_congr_cls F _ (fun i => isLB_toLB (Δ i)) hL e

theorem inter_comp_perm (Δ : Fin Y.dim → Y.Dv) (σ : Equiv.Perm (Fin Y.dim)) :
    Y.inter (Δ ∘ σ) = Y.inter Δ :=
  interNum_comp_perm F _ (L := fun i => Y.lb (Δ i)) (fun i => isLB_toLB (Δ i)) σ

theorem inter_const (Δ : Y.Dv) : Y.inter (fun _ => Δ) = topSelfIntersection F (Y.lb Δ) Y.dim := rfl

theorem diffVanish_chi : DiffVanish (Y.dim + 1) Y.chi :=
  (diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq])).comap toPic

def interForm : MultilinearMap ℤ (fun _ : Fin Y.dim => Y.Dv) ℤ := Y.diffVanish_chi.form

@[simp] theorem interForm_apply (Δ : Fin Y.dim → Y.Dv) : Y.interForm Δ = Y.inter Δ :=
  (Y.diffVanish_chi.form_apply Δ 0).trans (Y.inter_eq_multiDiff Δ).symm

theorem inter_zsmul (n : Fin Y.dim → ℤ) (Δ : Fin Y.dim → Y.Dv) :
    Y.inter (fun i => n i • Δ i) = (∏ i, n i) * Y.inter Δ := by
  simp only [← interForm_apply, MultilinearMap.map_smul_univ, smul_eq_mul]

theorem inter_const_nsmul (n : ℕ) (Δ : Y.Dv) :
    Y.inter (fun _ => n • Δ) = (n : ℤ) ^ Y.dim * Y.inter fun _ => Δ := by
  simpa using Y.inter_zsmul (fun _ => n) fun _ => Δ

def IsCurve (Z : Y.Cl) : Prop :=
  IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1

def deg (C : Y.Cl) (Δ : Y.Dv) : ℤ := interNumRed F C ![Y.lb Δ]

theorem isCurve_iff (Z : Y.Cl) : Y.IsCurve Z ↔ IsCompleteCurve F Z := (Y.isCompleteCurve_iff Z).symm

variable {Y}

theorem deg_principal (C : Y.Cl) (g : Y.Fnˣ) : Y.deg C (principal g) = 0 :=
  interNumRed_one_eq_zero (isLB_toLB _) (toPic_principal g) C

@[simp] theorem deg_zero (C : Y.Cl) : Y.deg C 0 = 0 := deg_principal C 1

namespace IsCurve

variable {C : Y.Cl} (hC : Y.IsCurve C)

include hC

theorem deg_nonneg_of_generatesAt {Δ : Y.Dv} {f : Y.Fn} (hf : f ∈ Y.H0 Δ) {x : Y.X} (hx : x ∈ C)
    (h : Δ.GeneratesAt x f) :
    0 ≤ Y.deg C Δ ∧ ((∃ y ∈ C, Δ.VanishesAt y f) → 0 < Y.deg C Δ) := by
  have e := rat_sec (⟨f, hf⟩ : Y.H0 Δ)
  have H := ((Y.isCurve_iff C).1 hC).interNumRed_nonneg_of_sec Y.isAmple_projective_O_one (isLB_toLB Δ)
    (sec ⟨f, hf⟩) hx (((presents_toLB Δ).generatesAt_rat_iff _).1 (e.symm ▸ h))
  exact ⟨H.1, fun ⟨y, hy, hy'⟩ =>
    H.2 ⟨y, hy, ((presents_toLB Δ).vanishesAt_rat_iff _).1 (e.symm ▸ hy')⟩⟩

end IsCurve

variable (Y) in

def nef (Δ : Y.Dv) : Prop := IsNef F (Y.lb Δ)

variable (Y) in

def big (Δ : Y.Dv) : Prop := IsBig F (Y.lb Δ)

variable (Y) in

def ample (Δ : Y.Dv) : Prop := IsAmpleLB (Y.lb Δ)

variable {Δ A B : Y.Dv} {L : LB Y.X}

theorem nef_iff : Y.nef Δ ↔ ∀ C, Y.IsCurve C → 0 ≤ Y.deg C Δ :=
  ⟨fun h C hC => h.2 C ((Y.isCurve_iff C).1 hC),
    fun h => ⟨isLB_toLB Δ, fun C hC => h C ((Y.isCurve_iff C).2 hC)⟩⟩

theorem bpf.nef {V : Set Y.Fn} (h : Y.bpf Δ V) : Y.nef Δ := nef_iff.2 fun _ hC => by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  obtain ⟨f, hf, hfx⟩ := h.2 x
  exact (hC.deg_nonneg_of_generatesAt (h.mem f hf) hx hfx).1

end Var

end GlobalTheory.ProjVar
