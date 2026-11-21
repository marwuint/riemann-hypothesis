import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OntoDef

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.CompHS
open GlobalTheory.AllWt (secZ exOf)
open GlobalTheory.FlagMod (FlagCover)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Flag

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

def vanOut (e : Ix Dw → ℤ) : Submodule c.F (H0 (flagStr X) (X.LL e) ⊤) where
  carrier := {s | ∀ y, y ∉ flagOpen X → ∀ i hi, germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal _}
  zero_mem' y _ i hi := by rw [map_zero]; exact zero_mem _
  add_mem' hs ht y hy i hi := by rw [map_add]; exact add_mem (hs y hy i hi) (ht y hy i hi)
  smul_mem' a s hs y hy i hi := by rw [germ_smul]; exact Ideal.mul_mem_left _ _ (hs y hy i hi)

def ruleTop (e : Ix Dw → ℤ) : H0 (flagStr X) (X.LL e) ⊤ →ₗ[c.F] Rul Xo c :=
  (secZ Xo c e).subtype ∘ₗ (secOf X e).symm.toLinearMap ∘ₗ restr le_top

def extZ (e : Ix Dw → ℤ) : Submodule c.F (Rul Xo c) := LinearMap.range (ruleTop X e)

def extVanZ (e : Ix Dw → ℤ) : Submodule c.F (Rul Xo c) := (vanOut X e).map (ruleTop X e)

variable {X} {e : Ix Dw → ℤ}

theorem mem_vanOut {s : H0 (flagStr X) (X.LL e) ⊤} :
    s ∈ vanOut X e ↔ ∀ y, y ∉ flagOpen X → y ∉ nonzeroLocus (toSec s) := by
  refine forall₂_congr fun y _ => ⟨fun h hy => ?_, fun h i hi hu => h ((isUnit_ger_iff _ hi).1 (by rwa [ger_toSec]))⟩
  obtain ⟨i, hi⟩ := exists_chart (X.F.isLB_LL e) y
  exact h i hi (by rw [← ger_toSec]; exact (isUnit_ger_iff _ hi).2 hy)

theorem mem_vanOut_iff_le {s : H0 (flagStr X) (X.LL e) ⊤} :
    s ∈ vanOut X e ↔ nonzeroLocus (toSec s) ≤ flagOpen X :=
  mem_vanOut.trans (forall_congr' fun _ => not_imp_not)

theorem ruleTop_mem_secZ (s : H0 (flagStr X) (X.LL e) ⊤) : ruleTop X e s ∈ secZ Xo c e :=
  ((secOf X e).symm (restr le_top s)).2

theorem secOf_ruleTop (s : H0 (flagStr X) (X.LL e) ⊤) :
    secOf X e ⟨ruleTop X e s, ruleTop_mem_secZ s⟩ = restr le_top s :=
  (secOf X e).apply_symm_apply _

theorem ruleTop_eq_iff {s : H0 (flagStr X) (X.LL e) ⊤} {f : Rul Xo c} :
    ruleTop X e s = f ↔ ∃ hf : f ∈ secZ Xo c e, restr le_top s = secOf X e ⟨f, hf⟩ :=
  ⟨fun h => h ▸ ⟨ruleTop_mem_secZ s, (secOf_ruleTop s).symm⟩,
    fun ⟨_, h⟩ => congrArg Subtype.val ((secOf X e).symm_apply_eq.2 h)⟩

variable (X e) in

theorem ruleTop_injective : Function.Injective (ruleTop X e) :=
  Subtype.val_injective.comp ((secOf X e).symm.injective.comp (restr_injective_of_dense le_top (dense_flagOpen X)))

open Classical in

theorem evR_ruleTop {S : Type} [CommRing S] [Algebra c.F S] [_root_.IsReduced S] (s : H0 (flagStr X) (X.LL e) ⊤)
    {P Q : FrPt Xo c S} {k : X.F.J} {z : Sp S ⟶ X.YY} {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X)
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k z hz Q) (ht : FrBor t Q P) :
    evR Xo c (ruleTop X e s) P = (∏ ix, t ix ^ e ix).val * H0.val (B := X.LL e) z k le_top hz s := by
  refine (evR_eq_val_secOf ⟨_, ruleTop_mem_secZ s⟩ hO hQ ht).trans (congrArg (_ * ·) ?_)
  rw [secOf_ruleTop]
  exact evalPt_res z (inf_le_inf_right _ le_top) (FlagMod.le_preimage_inf le_top hz) (FlagMod.le_preimage_inf hO hz) _

theorem mem_extZ {f : Rul Xo c} : f ∈ extZ X e ↔
    ∃ hf : f ∈ secZ Xo c e, ∃ s : H0 (flagStr X) (X.LL e) ⊤, restr le_top s = secOf X e ⟨f, hf⟩ :=
  ⟨fun ⟨s, h⟩ => (ruleTop_eq_iff.1 h).imp fun _ h => ⟨s, h⟩, fun ⟨hf, s, h⟩ => ⟨s, ruleTop_eq_iff.2 ⟨hf, h⟩⟩⟩

theorem ruleTop_mem_extVanZ {s : H0 (flagStr X) (X.LL e) ⊤} : ruleTop X e s ∈ extVanZ X e ↔ s ∈ vanOut X e :=
  ⟨fun ⟨_, hs, h⟩ => ruleTop_injective X e h ▸ hs, fun h => ⟨s, h, rfl⟩⟩

variable (X e) in

theorem extVanZ_le_extZ : extVanZ X e ≤ extZ X e := LinearMap.map_le_range

variable (X e) in

theorem extZ_le_secZ : extZ X e ≤ secZ Xo c e := fun _ h => (mem_extZ.1 h).1

variable (X e) in

theorem extVanZ_le_secZ : extVanZ X e ≤ secZ Xo c e := (extVanZ_le_extZ X e).trans (extZ_le_secZ X e)

variable (X e) in

def vanOutEquiv : vanOut X e ≃ₗ[c.F] extVanZ X e :=
  Submodule.equivMapOfInjective _ (ruleTop_injective X e) _

@[simp] theorem coe_vanOutEquiv (s : vanOut X e) : (vanOutEquiv X e s : Rul Xo c) = ruleTop X e s := rfl

variable (X e) in

def extEquiv : H0 (flagStr X) (X.LL e) ⊤ ≃ₗ[c.F] extZ X e := LinearEquiv.ofInjective _ (ruleTop_injective X e)

@[simp] theorem coe_extEquiv (s : H0 (flagStr X) (X.LL e) ⊤) : (extEquiv X e s : Rul Xo c) = ruleTop X e s := rfl

theorem germ_pull_inc₀_mem {s : H0 (flagStr X) (X.LL e) ⊤} (hs : s ∈ vanOut X e) (Z : Comp Xo c) :
    ∀ y ∈ bd₀ X Z, ∀ i hi, germ (B := LL₀ X Z e) i y (memTop y) hi (H0.pull (inc₀ X Z) le_top s) ∈
      IsLocalRing.maximalIdeal _ := fun y hy i hi hu =>
  hs _ hy _ _ (isUnit_of_map_unit ((inc₀ X Z).stalkMap y).hom _ (germ_pull (inc₀ X Z) _ i y (memTop y) hi s ▸ hu))

theorem pull_inc₀_mem_vanBd {la : AllWt.Weight Dw} {s : H0 (flagStr X) (X.LL (exOf Dw la 0)) ⊤}
    (hs : s ∈ vanOut X (exOf Dw la 0)) (Z : Comp Xo c) : H0.pull (inc₀ X Z) le_top s ∈ vanBd X Z la :=
  germ_pull_inc₀_mem hs Z

theorem sec₀_ruleTop (s : H0 (flagStr X) (X.LL e) ⊤) (Z : Comp Xo c) :
    sec₀ X Z e ⟨ruleTop X e s, ruleTop_mem_secZ s⟩ = restr le_top (H0.pull (inc₀ X Z) le_top s) := by
  refine (congrArg (H0.pull (inc₀ X Z) (le_refl (U₀ X Z))) (secOf_ruleTop s)).trans
    ((pull_restr _ _ _ _).trans (ext_germ fun y hy => ?_))
  obtain ⟨i, hi⟩ := exists_chart (LB.isLB_pull (X.F.isLB_LL e) (inc₀ X Z)) y
  exact ⟨i, hi, (germ_pull (inc₀ X Z) _ i y hy hi s).trans
    ((germ_restr _ _ _ _ _ _).trans (germ_pull (inc₀ X Z) _ i y (memTop y) hi s)).symm⟩

theorem exists_vanBd_of_mem_extVanZ {la : AllWt.Weight Dw} {f : secZ Xo c (exOf Dw la 0)}
    (hf : f.1 ∈ extVanZ X (exOf Dw la 0)) (Z : Comp Xo c) :
    ∃ s ∈ vanBd X Z la, restr le_top s = sec₀ X Z _ f := by
  obtain ⟨f, hf'⟩ := f
  obtain ⟨s, hs, rfl⟩ := hf
  exact ⟨_, pull_inc₀_mem_vanBd hs Z, (sec₀_ruleTop s Z).symm⟩

end Flag

variable (T : TorFlag Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)

end GlobalTheory.CompanionTheory.Ar.OntoDef
