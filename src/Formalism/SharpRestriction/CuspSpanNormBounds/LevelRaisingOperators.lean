import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.FormalDegreeBessel.FinalIO
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def SmU (U : Set (Fin m → ℂ)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ ((Fin m → ℂ) → E) where
  carrier := {f | ContDiffOn ℝ ∞ f U ∧ ∀ x, x ∉ U → f x = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun a {f} hf => ⟨hf.1.const_smul a, fun x hx => by simp [hf.2 x hx]⟩

structure GoodOp (U : Set (Fin m → ℂ)) (O : Op m E) : Prop where
  smooth : ∀ f, ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (O f) U
  add : ∀ f g, ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ∀ x ∈ U, O (f + g) x = O f x + O g x
  smul : ∀ (a : ℂ) f, ContDiffOn ℝ ∞ f U → ∀ x ∈ U, O (a • f) x = a • O f x
  loc : ∀ f g, (∀ x ∈ U, f x = g x) → ∀ x ∈ U, O f x = O g x

open Classical in

def toEnd (U : Set (Fin m → ℂ)) (O : Op m E) : Module.End ℂ (SmU U E) :=
  if h : GoodOp U O then
    { toFun := fun φ => ⟨U.indicator (O φ.1),
        (h.smooth _ φ.2.1).congr (fun x hx => Set.indicator_of_mem hx _),
        fun x hx => Set.indicator_of_notMem hx _⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext; funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx, h.add _ _ φ.2.1 ψ.2.1 x hx]
        · simp [Set.indicator_of_notMem hx]
      map_smul' := fun a φ => by
        apply Subtype.ext; funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx, h.smul a _ φ.2.1 x hx]
        · simp [Set.indicator_of_notMem hx] }
  else 0

variable {U : Set (Fin m → ℂ)}

theorem toEnd_apply {O : Op m E} (h : GoodOp U O) (φ : SmU U E) {x : Fin m → ℂ} (hx : x ∈ U) :
    (toEnd U O φ).1 x = O φ.1 x := by
  simp [toEnd, h, Set.indicator_of_mem hx]

theorem end_ext {a b : Module.End ℂ (SmU U E)} (h : ∀ φ : SmU U E, ∀ x ∈ U, (a φ).1 x = (b φ).1 x) :
    a = b := by
  apply LinearMap.ext; intro φ; apply Subtype.ext; funext x
  by_cases hx : x ∈ U
  · exact h φ x hx
  · rw [(a φ).2.2 x hx, (b φ).2.2 x hx]

theorem contDiffOn_clm_apply' {e : (Fin m → ℂ) → E →L[ℂ] E} {f : (Fin m → ℂ) → E}
    (he : ContDiffOn ℝ ∞ e U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (fun x => e x (f x)) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => (e x).restrictScalars ℝ) U :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff).comp_contDiffOn he
  exact h1.clm_apply hf

def opD (u w : Fin m → ℂ) (s : ℂ) : Op m E := fun φ x => Wc u w s (fderiv ℝ φ x)

theorem good_mulF {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) : GoodOp U (mulF (E := E) f) where
  smooth := fun g hg => hf.smul hg
  add := fun g g' _ _ x _ => by simp [mulF]
  smul := fun a g _ x _ => by simp only [mulF, Pi.smul_apply]; exact smul_comm _ _ _
  loc := fun g g' h x hx => by simp [mulF, h x hx]

theorem good_mulE {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) : GoodOp U (mulE e) where
  smooth := fun g hg => contDiffOn_clm_apply' he hg
  add := fun g g' _ _ x _ => by simp [mulE]
  smul := fun a g _ x _ => by simp [mulE]
  loc := fun g g' h x hx => by simp [mulE, h x hx]

theorem cda (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (Fin m → ℂ) → F}
    (hf : ContDiffOn ℝ ∞ f U) {x : Fin m → ℂ} (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
  hf.contDiffAt (hU.mem_nhds hx)

theorem Wc_smul_const (u w : Fin m → ℂ) (s a : ℂ) (T : (Fin m → ℂ) →L[ℝ] E) :
    Wc u w s (a • T) = a • Wc u w s T := by
  simp only [Wc_apply, _root_.smul_apply]
  module

theorem good_opD (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) : GoodOp U (opD (E := E) u w s) where
  smooth := fun g hg x hx => (contDiffAt_Wc (cda hU hg hx) u w s).contDiffWithinAt
  add := fun g g' hg hg' x hx => by
    simp only [opD]
    rw [fderiv_add (diff_of_reg (cda hU hg hx)) (diff_of_reg (cda hU hg' hx)), map_add]
  smul := fun a g hg x hx => by
    simp only [opD]
    rw [fderiv_const_smul (diff_of_reg (cda hU hg hx)) a, Wc_smul_const]
  loc := fun g g' h x hx => by
    simp only [opD]
    have : g =ᶠ[𝓝 x] g' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
    rw [this.fderiv_eq]

def fn (U : Set (Fin m → ℂ)) (f : (Fin m → ℂ) → ℂ) : Module.End ℂ (SmU U E) := toEnd U (mulF f)

def fe (U : Set (Fin m → ℂ)) (e : (Fin m → ℂ) → E →L[ℂ] E) : Module.End ℂ (SmU U E) := toEnd U (mulE e)

def dd (U : Set (Fin m → ℂ)) (u w : Fin m → ℂ) (s : ℂ) : Module.End ℂ (SmU U E) := toEnd U (opD u w s)

theorem fn_apply {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (φ : SmU U E) {x : Fin m → ℂ}
    (hx : x ∈ U) : (fn U f φ).1 x = f x • φ.1 x := toEnd_apply (good_mulF hf) φ hx

theorem fe_apply {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : (fe U e φ).1 x = e x (φ.1 x) := toEnd_apply (good_mulE he) φ hx

theorem dd_apply (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (φ : SmU U E) {x : Fin m → ℂ}
    (hx : x ∈ U) : (dd U u w s φ).1 x = Wc u w s (fderiv ℝ φ.1 x) := toEnd_apply (good_opD hU u w s) φ hx

theorem fderiv_congr_on (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g g' : (Fin m → ℂ) → F} (h : ∀ x ∈ U, g x = g' x) {x : Fin m → ℂ} (hx : x ∈ U) :
    fderiv ℝ g x = fderiv ℝ g' x :=
  (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h).fderiv_eq

theorem fderiv_fn (hU : IsOpen U) {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : fderiv ℝ (fn U f φ).1 x = fderiv ℝ (fun y => f y • φ.1 y) x :=
  fderiv_congr_on hU (fun _ hy => fn_apply hf φ hy) hx

theorem fderiv_fe (hU : IsOpen U) {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) : fderiv ℝ (fe U e φ).1 x = fderiv ℝ (fun y => e y (φ.1 y)) x :=
  fderiv_congr_on hU (fun _ hy => fe_apply he φ hy) hx

theorem fderiv_dd (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (φ : SmU U E)
    {x : Fin m → ℂ} (hx : x ∈ U) :
    fderiv ℝ (dd U u w s φ).1 x = fderiv ℝ (fun y => Wc u w s (fderiv ℝ φ.1 y)) x :=
  fderiv_congr_on hU (fun _ hy => dd_apply hU u w s φ hy) hx

theorem Wc_clm {e : (Fin m → ℂ) → E →L[ℂ] E} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (he : DifferentiableAt ℝ e x) (hh : DifferentiableAt ℝ h x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => e y (h y)) x) =
      (Wc u w s (fderiv ℝ e x)) (h x) + e x (Wc u w s (fderiv ℝ h x)) := by
  have h1 : HasFDerivAt (fun y => (e y).restrictScalars ℝ)
      ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E)).comp (fderiv ℝ e x)) x :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp x he.hasFDerivAt
  have h2 := h1.clm_apply hh.hasFDerivAt
  have h3 : fderiv ℝ (fun y => e y (h y)) x = _ := h2.fderiv
  rw [h3]
  have e1 : ∀ v, (ContinuousLinearMap.restrictScalars ℝ (e x) ∘SL fderiv ℝ h x +
      ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E)) ∘SL fderiv ℝ e x).flip (h x)) v =
      e x (fderiv ℝ h x v) + (fderiv ℝ e x v) (h x) := fun v => rfl
  rw [Wc_apply, Wc_apply, Wc_apply, e1, e1]
  simp only [_root_.add_apply, _root_.smul_apply, map_add, map_smul]
  module

theorem fn_comm {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    fn (E := E) U f * fn U g = fn U g * fn U f := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fn_apply hg _ hx]
  exact smul_comm _ _ _

theorem fn_mul_one {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (h : ∀ x ∈ U, f x * g x = 1) : fn (E := E) U f * fn U g = 1 := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fn_apply hg _ hx, smul_smul, h x hx, one_smul,
    Module.End.one_apply]

theorem fn_fe_comm {f : (Fin m → ℂ) → ℂ} {e : (Fin m → ℂ) → E →L[ℂ] E} (hf : ContDiffOn ℝ ∞ f U)
    (he : ContDiffOn ℝ ∞ e U) : fn U f * fe U e = fe U e * fn U f := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, fn_apply hf _ hx, fe_apply he _ hx, map_smul]

theorem contDiffOn_Wc (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : (Fin m → ℂ) → F} (hf : ContDiffOn ℝ ∞ f U) (u w : Fin m → ℂ) (s : ℂ) :
    ContDiffOn ℝ ∞ (fun y => Wc u w s (fderiv ℝ f y)) U :=
  fun _ hx => (contDiffAt_Wc (cda hU hf hx) u w s).contDiffWithinAt

theorem dd_fn (hU : IsOpen U) {f : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (u w : Fin m → ℂ) (s : ℂ) :
    dd (E := E) U u w s * fn U f = fn U f * dd U u w s + fn U (fun y => Wc u w s (fderiv ℝ f y)) := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    fn_apply hf _ hx, fn_apply (contDiffOn_Wc hU hf u w s) _ hx, dd_apply hU _ _ _ _ hx, fderiv_fn hU hf _ hx]
  rw [Wc_smul (diff_of_reg (cda hU hf hx)) (diff_of_reg (cda hU φ.2.1 hx)), add_comm]

theorem dd_fe (hU : IsOpen U) {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U)
    (u w : Fin m → ℂ) (s : ℂ) :
    dd U u w s * fe U e = fe U e * dd U u w s + fe U (fun y => Wc u w s (fderiv ℝ e y)) := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    fe_apply he _ hx, fe_apply (contDiffOn_Wc hU he u w s) _ hx, dd_apply hU _ _ _ _ hx, fderiv_fe hU he _ hx]
  rw [Wc_clm (diff_of_reg (cda hU he hx)) (diff_of_reg (cda hU φ.2.1 hx)), add_comm]

theorem dd_comm (hU : IsOpen U) (u w : Fin m → ℂ) (s : ℂ) (u' w' : Fin m → ℂ) (s' : ℂ) :
    dd (E := E) U u w s * dd U u' w' s' = dd U u' w' s' * dd U u w s := by
  apply end_ext; intro φ x hx
  simp only [Module.End.mul_apply, dd_apply hU _ _ _ _ hx, fderiv_dd hU _ _ _ _ hx]
  exact Wc_comm (cda hU φ.2.1 hx) u w s u' w' s'

theorem fn_congr {f g : (Fin m → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f U) (h : ∀ x ∈ U, f x = g x) :
    fn (E := E) U f = fn U g := by
  have hg : ContDiffOn ℝ ∞ g U := hf.congr (fun x hx => (h x hx).symm)
  apply end_ext; intro φ x hx
  rw [fn_apply hf _ hx, fn_apply hg _ hx, h x hx]

theorem fn_zero : fn (E := E) U (fun _ => 0) = 0 := by
  apply end_ext; intro φ x hx
  rw [fn_apply contDiffOn_const _ hx]; simp

theorem fn_const (a : ℂ) : fn (E := E) U (fun _ => a) = algebraMap ℂ _ a := by
  apply end_ext; intro φ x hx
  rw [fn_apply contDiffOn_const _ hx]; simp [Module.algebraMap_end_apply]

theorem fe_zero_of {e : (Fin m → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e U) (h : ∀ x ∈ U, e x = 0) :
    fe U e = 0 := by
  apply end_ext; intro φ x hx
  rw [fe_apply he _ hx, h x hx]; simp

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section RingLemmas
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem der_mul {d f g k k' : A} (h1 : d * f = f * d + k) (h2 : d * g = g * d + k') :
    d * (f * g) = (f * g) * d + (k * g + f * k') := by
  rw [← mul_assoc, h1, add_mul, mul_assoc, h2]; noncomm_ring

theorem der_inv {d f fi k : A} (h : d * f = f * d + k) (h1 : f * fi = 1) (h2 : fi * f = 1) :
    d * fi = fi * d - fi * k * fi := by
  have e : f * d = d * f - k := by rw [h]; abel
  calc d * fi = (fi * f) * d * fi := by rw [h2, one_mul]
    _ = fi * (f * d) * fi := by noncomm_ring
    _ = fi * d * (f * fi) - fi * k * fi := by rw [e]; noncomm_ring
    _ = fi * d - fi * k * fi := by rw [h1, mul_one]

theorem der_GG {d z zb a b : A} (t : ℂ) (h1 : d * z = z * d + a) (h2 : d * zb = zb * d + b) :
    d * (z * zb - algebraMap ℂ A t) = (z * zb - algebraMap ℂ A t) * d + (a * zb + z * b) := by
  rw [mul_sub, sub_mul, der_mul h1 h2, Algebra.commutes t d]; abel

theorem der_left {x d f k : A} (hx : x * f = f * x) (h : d * f = f * d + k) :
    (x * d) * f = f * (x * d) + x * k := by
  rw [mul_assoc, h, mul_add, ← mul_assoc, hx, mul_assoc]

end RingLemmas

structure Setup (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  U : Set (Fin (r + 1) → ℂ)
  T : ℝ
  T' : ℝ
  h : (Fin (r + 1) → ℂ) → E →L[ℂ] E
  hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E
  isOpen : IsOpen U
  sub : ∀ x ∈ U, x ∈ OmX (r + 1)
  pos : ∀ x ∈ U, T * T' < Complex.normSq (zOf x)
  h_sm : ContDiffOn ℝ ∞ h U
  hs_sm : ContDiffOn ℝ ∞ hs U
  h_c : ∀ x ∈ U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ h x (Pi.single a.castSucc v) = 0
  hs_c : ∀ x ∈ U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ hs x (Pi.single a.castSucc v) = 0

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

abbrev Rg := Module.End ℂ (SmU S.U E)

def X (k : Fin (r + 1)) (i : Fin 6) : S.Rg := fn S.U (coef k i)

def dW (k : Fin (r + 1)) : S.Rg := dd S.U (Pi.single k 1) (Pi.single k Complex.I) (-Complex.I)

def dWb (k : Fin (r + 1)) : S.Rg := dd S.U (Pi.single k 1) (Pi.single k Complex.I) Complex.I

def P (k : Fin (r + 1)) : S.Rg := S.X k 1 * S.dW k

def Pb (k : Fin (r + 1)) : S.Rg := S.X k 4 * S.dWb k
def gG : S.Rg := fn S.U (GG S.T S.T')
def gGi : S.Rg := fn S.U (fun x => (GG S.T S.T' x)⁻¹)
def nab : S.Rg := S.dW (Fin.last r) + fe S.U S.h
def nabs : S.Rg := -S.dWb (Fin.last r) + fe S.U S.hs

theorem hc (k : Fin (r + 1)) (i : Fin 6) : ContDiffOn ℝ ∞ (coef k i) S.U :=
  fun x hx => (coef_contDiffAt (S.sub x hx) i).contDiffWithinAt

theorem GG_eq (x : Fin (r + 1) → ℂ) :
    GG S.T S.T' x = coef (Fin.last r) 1 x * coef (Fin.last r) 4 x - ((S.T * S.T' : ℝ) : ℂ) := by
  simp only [GG, coef, zOf]
  rw [Complex.ofReal_sub, ← Complex.mul_conj]; rfl

theorem GG_ne {x : Fin (r + 1) → ℂ} (hx : x ∈ S.U) : GG S.T S.T' x ≠ 0 := by
  simp only [GG]
  have := S.pos x hx
  exact_mod_cast (sub_pos.2 this).ne'

theorem hGG : ContDiffOn ℝ ∞ (GG S.T S.T') S.U := by
  have : ContDiffOn ℝ ∞ (fun x => coef (Fin.last r) 1 x * coef (Fin.last r) 4 x - ((S.T * S.T' : ℝ) : ℂ)) S.U :=
    ((S.hc _ 1).mul (S.hc _ 4)).sub contDiffOn_const
  exact this.congr (fun x _ => S.GG_eq x)

theorem hGGi : ContDiffOn ℝ ∞ (fun x => (GG S.T S.T' x)⁻¹) S.U :=
  S.hGG.inv (fun _ hx => S.GG_ne hx)

theorem X_comm (k k' : Fin (r + 1)) (i i' : Fin 6) : S.X k i * S.X k' i' = S.X k' i' * S.X k i :=
  fn_comm (S.hc k i) (S.hc k' i')

theorem gG_def : S.gG = S.X (Fin.last r) 1 * S.X (Fin.last r) 4 - algebraMap ℂ S.Rg ((S.T * S.T' : ℝ) : ℂ) := by
  apply end_ext; intro φ x hx
  simp only [gG, X, LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
    fn_apply S.hGG _ hx, fn_apply (S.hc _ _) _ hx, Module.algebraMap_end_apply, Submodule.coe_smul,
    Pi.smul_apply, S.GG_eq, sub_smul, mul_smul]

theorem dW_X (j k : Fin (r + 1)) (i : Fin 6) :
    S.dW j * S.X k i = S.X k i * S.dW j +
      fn S.U (fun y => if (i : ℕ) < 3 ∧ j = k then ck k i y else 0) := by
  rw [dW, X, dd_fn S.isOpen (S.hc k i)]
  congr 1
  apply fn_congr (contDiffOn_Wc S.isOpen (S.hc k i) _ _ _)
  intro x hx
  rw [← wirt_eq, wirt_coef (S.sub x hx)]

theorem dWb_X (j k : Fin (r + 1)) (i : Fin 6) :
    S.dWb j * S.X k i = S.X k i * S.dWb j +
      fn S.U (fun y => if ¬ (i : ℕ) < 3 ∧ j = k then ck k i y else 0) := by
  rw [dWb, X, dd_fn S.isOpen (S.hc k i)]
  congr 1
  apply fn_congr (contDiffOn_Wc S.isOpen (S.hc k i) _ _ _)
  intro x hx
  rw [← wirtBar_eq, wirtBar_coef (S.sub x hx)]

theorem fn_one' : fn (E := E) S.U (fun _ => 1) = 1 := by
  rw [fn_const]; simp

theorem holo_deriv_coord_commutator (j k : Fin (r + 1)) : S.dW j * S.X k 1 = S.X k 1 * S.dW j + (if j = k then 1 else 0) := by
  rw [dW_X]; congr 1
  by_cases h : j = k
  · simp [h, ck, fn_one']
  · simp [h, fn_zero]

theorem holo_deriv_commute_conj_coord (j k : Fin (r + 1)) : S.dW j * S.X k 4 = S.X k 4 * S.dW j := by
  rw [dW_X]; simp [fn_zero]

theorem antiholo_deriv_commute_coord (j k : Fin (r + 1)) : S.dWb j * S.X k 1 = S.X k 1 * S.dWb j := by
  rw [dWb_X]; simp [fn_zero]

theorem antiholo_deriv_conj_coord_commutator (j k : Fin (r + 1)) : S.dWb j * S.X k 4 = S.X k 4 * S.dWb j + (if j = k then 1 else 0) := by
  rw [dWb_X]; congr 1
  by_cases h : j = k
  · simp [h, ck, fn_one']
  · simp [h, fn_zero]

theorem coord_mul_inv_coord_eq_one (k : Fin (r + 1)) : S.X k 1 * S.X k 2 = 1 :=
  fn_mul_one (S.hc k 1) (S.hc k 2) (fun x hx => mul_inv_cancel₀ (S.sub x hx k))
theorem inv_coord_mul_coord_eq_one (k : Fin (r + 1)) : S.X k 2 * S.X k 1 = 1 := by rw [X_comm, coord_mul_inv_coord_eq_one]
theorem conj_coord_mul_conj_inv_eq_one (k : Fin (r + 1)) : S.X k 4 * S.X k 5 = 1 :=
  fn_mul_one (S.hc k 4) (S.hc k 5) (fun x hx => mul_inv_cancel₀ (by simpa [coef] using S.sub x hx k))
theorem conj_inv_mul_conj_coord_eq_one (k : Fin (r + 1)) : S.X k 5 * S.X k 4 = 1 := by rw [X_comm, conj_coord_mul_conj_inv_eq_one]

theorem holo_deriv_inv_coord_commutator (j k : Fin (r + 1)) :
    S.dW j * S.X k 2 = S.X k 2 * S.dW j - (if j = k then S.X k 2 * S.X k 2 else 0) := by
  rw [der_inv (S.holo_deriv_coord_commutator j k) (S.coord_mul_inv_coord_eq_one k) (S.inv_coord_mul_coord_eq_one k)]
  by_cases h : j = k <;> simp [h]

theorem holo_deriv_commute_conj_inv_coord (j k : Fin (r + 1)) : S.dW j * S.X k 5 = S.X k 5 * S.dW j := by
  have := der_inv (k := 0) (by simpa using S.holo_deriv_commute_conj_coord j k) (S.conj_coord_mul_conj_inv_eq_one k) (S.conj_inv_mul_conj_coord_eq_one k)
  simpa using this

theorem antiholo_deriv_commute_inv_coord (j k : Fin (r + 1)) : S.dWb j * S.X k 2 = S.X k 2 * S.dWb j := by
  have := der_inv (k := 0) (by simpa using S.antiholo_deriv_commute_coord j k) (S.coord_mul_inv_coord_eq_one k) (S.inv_coord_mul_coord_eq_one k)
  simpa using this

theorem antiholo_deriv_conj_inv_commutator (j k : Fin (r + 1)) :
    S.dWb j * S.X k 5 = S.X k 5 * S.dWb j - (if j = k then S.X k 5 * S.X k 5 else 0) := by
  rw [der_inv (S.antiholo_deriv_conj_coord_commutator j k) (S.conj_coord_mul_conj_inv_eq_one k) (S.conj_inv_mul_conj_coord_eq_one k)]
  by_cases h : j = k <;> simp [h]

theorem momentum_coord_commutator (j k : Fin (r + 1)) : S.P j * S.X k 1 = S.X k 1 * S.P j + (if j = k then S.X k 1 else 0) := by
  rw [P, der_left (S.X_comm _ _ _ _) (S.holo_deriv_coord_commutator j k)]
  by_cases h : j = k <;> simp [h]

theorem momentum_inv_coord_commutator (j k : Fin (r + 1)) : S.P j * S.X k 2 = S.X k 2 * S.P j - (if j = k then S.X k 2 else 0) := by
  have := S.holo_deriv_inv_coord_commutator j k
  rw [sub_eq_add_neg] at this
  rw [P, der_left (S.X_comm _ _ _ _) this]
  by_cases h : j = k
  · subst h; simp [← mul_assoc, S.coord_mul_inv_coord_eq_one, sub_eq_add_neg]
  · simp [h]

theorem momentum_commute_conj_coord (j k : Fin (r + 1)) : S.P j * S.X k 4 = S.X k 4 * S.P j := by
  have := der_left (k := 0) (S.X_comm j k 1 4) (by simpa using S.holo_deriv_commute_conj_coord j k)
  simpa [P] using this

theorem momentum_commute_conj_inv_coord (j k : Fin (r + 1)) : S.P j * S.X k 5 = S.X k 5 * S.P j := by
  have := der_left (k := 0) (S.X_comm j k 1 5) (by simpa using S.holo_deriv_commute_conj_inv_coord j k)
  simpa [P] using this

theorem conj_momentum_conj_coord_commutator (j k : Fin (r + 1)) : S.Pb j * S.X k 4 = S.X k 4 * S.Pb j + (if j = k then S.X k 4 else 0) := by
  rw [Pb, der_left (S.X_comm _ _ _ _) (S.antiholo_deriv_conj_coord_commutator j k)]
  by_cases h : j = k <;> simp [h]

theorem conj_momentum_conj_inv_commutator (j k : Fin (r + 1)) : S.Pb j * S.X k 5 = S.X k 5 * S.Pb j - (if j = k then S.X k 5 else 0) := by
  have := S.antiholo_deriv_conj_inv_commutator j k
  rw [sub_eq_add_neg] at this
  rw [Pb, der_left (S.X_comm _ _ _ _) this]
  by_cases h : j = k
  · subst h; simp [← mul_assoc, S.conj_coord_mul_conj_inv_eq_one, sub_eq_add_neg]
  · simp [h]

theorem conj_momentum_commute_coord (j k : Fin (r + 1)) : S.Pb j * S.X k 1 = S.X k 1 * S.Pb j := by
  have := der_left (k := 0) (S.X_comm j k 4 1) (by simpa using S.antiholo_deriv_commute_coord j k)
  simpa [Pb] using this

theorem conj_momentum_commute_inv_coord (j k : Fin (r + 1)) : S.Pb j * S.X k 2 = S.X k 2 * S.Pb j := by
  have := der_left (k := 0) (S.X_comm j k 4 2) (by simpa using S.antiholo_deriv_commute_inv_coord j k)
  simpa [Pb] using this

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

namespace Setup

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Setup r E)

theorem nab_der {f : (Fin (r + 1) → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f S.U) {k : S.Rg}
    (h : S.dW (Fin.last r) * fn S.U f = fn S.U f * S.dW (Fin.last r) + k) :
    S.nab * fn S.U f = fn S.U f * S.nab + k := by
  rw [nab, add_mul, h, ← fn_fe_comm hf S.h_sm, mul_add]; abel

theorem nabs_der {f : (Fin (r + 1) → ℂ) → ℂ} (hf : ContDiffOn ℝ ∞ f S.U) {k : S.Rg}
    (h : S.dWb (Fin.last r) * fn S.U f = fn S.U f * S.dWb (Fin.last r) + k) :
    S.nabs * fn S.U f = fn S.U f * S.nabs - k := by
  rw [nabs, add_mul, neg_mul, h, ← fn_fe_comm hf S.hs_sm, mul_add, mul_neg]; abel

theorem nab_X {k : Fin (r + 1)} {i : Fin 6} {K : S.Rg}
    (h : S.dW (Fin.last r) * S.X k i = S.X k i * S.dW (Fin.last r) + K) :
    S.nab * S.X k i = S.X k i * S.nab + K := S.nab_der (S.hc k i) h

theorem nabs_X {k : Fin (r + 1)} {i : Fin 6} {K : S.Rg}
    (h : S.dWb (Fin.last r) * S.X k i = S.X k i * S.dWb (Fin.last r) + K) :
    S.nabs * S.X k i = S.X k i * S.nabs - K := S.nabs_der (S.hc k i) h

theorem gG_gGi : S.gG * S.gGi = 1 :=
  fn_mul_one S.hGG S.hGGi (fun _ hx => mul_inv_cancel₀ (S.GG_ne hx))
theorem gGi_gG : S.gGi * S.gG = 1 :=
  fn_mul_one S.hGGi S.hGG (fun _ hx => inv_mul_cancel₀ (S.GG_ne hx))

theorem der_gG {d a b : S.Rg} (h1 : d * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * d + a)
    (h2 : d * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * d + b) :
    d * S.gG = S.gG * d + (a * S.X (Fin.last r) 4 + S.X (Fin.last r) 1 * b) := by
  rw [gG_def]; exact der_GG _ h1 h2

theorem der_gGi {d a b : S.Rg} (h1 : d * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * d + a)
    (h2 : d * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * d + b) :
    d * S.gGi = S.gGi * d - S.gGi * (a * S.X (Fin.last r) 4 + S.X (Fin.last r) 1 * b) * S.gGi :=
  der_inv (S.der_gG h1 h2) S.gG_gGi S.gGi_gG

theorem ne_last (l : Fin r) : l.castSucc ≠ Fin.last r := (Fin.castSucc_lt_last l).ne
theorem last_ne (l : Fin r) : Fin.last r ≠ l.castSucc := (Fin.castSucc_lt_last l).ne'

theorem dW_dW (j k : Fin (r + 1)) : Commute (S.dW j) (S.dW k) := dd_comm S.isOpen _ _ _ _ _ _
theorem dW_dWb (j k : Fin (r + 1)) : Commute (S.dW j) (S.dWb k) := dd_comm S.isOpen _ _ _ _ _ _
theorem dWb_dWb (j k : Fin (r + 1)) : Commute (S.dWb j) (S.dWb k) := dd_comm S.isOpen _ _ _ _ _ _

theorem Wc_zero_of {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {T : (Fin (r + 1) → ℂ) →L[ℝ] F}
    {k : Fin (r + 1)} (h : ∀ v : ℂ, T (Pi.single k v) = 0) (s : ℂ) :
    Wc (Pi.single k 1) (Pi.single k Complex.I) s T = 0 := by
  rw [Wc_apply, h, h]; simp

theorem dW_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.dW l.castSucc) (fe S.U e) := by
  show _ * _ = _ * _
  rw [dW, dd_fe S.isOpen he, fe_zero_of (contDiffOn_Wc S.isOpen he _ _ _)
    (fun x hx => Wc_zero_of (hc x hx l) _), add_zero]

theorem dWb_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.dWb l.castSucc) (fe S.U e) := by
  show _ * _ = _ * _
  rw [dWb, dd_fe S.isOpen he, fe_zero_of (contDiffOn_Wc S.isOpen he _ _ _)
    (fun x hx => Wc_zero_of (hc x hx l) _), add_zero]

theorem X_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U) (k : Fin (r + 1)) (i : Fin 6) :
    Commute (S.X k i) (fe S.U e) := fn_fe_comm (S.hc k i) he

theorem euler_commute_mul_of_fderiv_eq_zero {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.P l.castSucc) (fe S.U e) := (S.X_fe he _ _).mul_left (S.dW_fe he hc l)

theorem Pb_fe {e : (Fin (r + 1) → ℂ) → E →L[ℂ] E} (he : ContDiffOn ℝ ∞ e S.U)
    (hc : ∀ x ∈ S.U, ∀ (a : Fin r) (v : ℂ), fderiv ℝ e x (Pi.single a.castSucc v) = 0) (l : Fin r) :
    Commute (S.Pb l.castSucc) (fe S.U e) := (S.X_fe he _ _).mul_left (S.dWb_fe he hc l)

theorem coord_commute_holo_deriv_of_ne {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.X j 1) (S.dW k) := by
  have := S.holo_deriv_coord_commutator k j
  simp only [h.symm, if_false, add_zero] at this
  exact this.symm

theorem conj_coord_commute_antiholo_deriv {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.X j 4) (S.dWb k) := by
  have := S.antiholo_deriv_conj_coord_commutator k j
  simp only [h.symm, if_false, add_zero] at this
  exact this.symm

theorem P_P (j k : Fin (r + 1)) : Commute (S.P j) (S.P k) := by
  by_cases h : j = k
  · subst h; exact Commute.refl _
  · exact ((show Commute (S.X j 1) (S.X k 1) from S.X_comm _ _ _ _).mul_right (S.coord_commute_holo_deriv_of_ne h)).mul_left
      ((S.coord_commute_holo_deriv_of_ne (Ne.symm h)).symm.mul_right (S.dW_dW j k))

theorem Pb_Pb (j k : Fin (r + 1)) : Commute (S.Pb j) (S.Pb k) := by
  by_cases h : j = k
  · subst h; exact Commute.refl _
  · exact ((show Commute (S.X j 4) (S.X k 4) from S.X_comm _ _ _ _).mul_right (S.conj_coord_commute_antiholo_deriv h)).mul_left
      ((S.conj_coord_commute_antiholo_deriv (Ne.symm h)).symm.mul_right (S.dWb_dWb j k))

theorem P_Pb (j k : Fin (r + 1)) : Commute (S.P j) (S.Pb k) :=
  ((show Commute (S.X j 1) (S.X k 4) from S.X_comm _ _ _ _).mul_right
    (show Commute (S.X j 1) (S.dWb k) from (S.antiholo_deriv_commute_coord k j).symm)).mul_left
    ((show Commute (S.dW j) (S.X k 4) from S.holo_deriv_commute_conj_coord j k).mul_right (S.dW_dWb j k))

theorem euler_commute_holo_deriv_of_ne {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.P j) (S.dW k) :=
  (S.coord_commute_holo_deriv_of_ne h).mul_left (S.dW_dW j k)
theorem euler_commute_antiholo_deriv (j k : Fin (r + 1)) : Commute (S.P j) (S.dWb k) :=
  (show Commute (S.X j 1) (S.dWb k) from (S.antiholo_deriv_commute_coord k j).symm).mul_left (S.dW_dWb j k)
theorem Pb_dW (j k : Fin (r + 1)) : Commute (S.Pb j) (S.dW k) :=
  (show Commute (S.X j 4) (S.dW k) from (S.holo_deriv_commute_conj_coord k j).symm).mul_left (S.dW_dWb k j).symm
theorem Pb_dWb {j k : Fin (r + 1)} (h : j ≠ k) : Commute (S.Pb j) (S.dWb k) :=
  (S.conj_coord_commute_antiholo_deriv h).mul_left (S.dWb_dWb j k)

theorem isFn_of_mem {x : S.Rg}
    (hx : x ∈ Set.range (fun l : Fin r => S.X l.castSucc 1) ∪ Set.range (fun l : Fin r => S.X l.castSucc 2) ∪
      Set.range (fun l : Fin r => S.X l.castSucc 4) ∪ Set.range (fun l : Fin r => S.X l.castSucc 5) ∪
      {S.X (Fin.last r) 1, S.X (Fin.last r) 2, S.X (Fin.last r) 4, S.X (Fin.last r) 5, S.gG, S.gGi}) :
    ∃ f, ContDiffOn ℝ ∞ f S.U ∧ x = fn S.U f := by
  rcases hx with (((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hx
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · exact ⟨_, S.hc _ _, rfl⟩
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hc _ _, rfl⟩
    · exact ⟨_, S.hGG, rfl⟩
    · exact ⟨_, S.hGGi, rfl⟩

open Formalism.FourierDecayAlt.R in

def lev : LevelData S.Rg r where
  p := fun l => S.P l.castSucc
  pb := fun l => S.Pb l.castSucc
  c := fun l => S.X l.castSucc 1
  ci := fun l => S.X l.castSucc 2
  cb := fun l => S.X l.castSucc 4
  cbi := fun l => S.X l.castSucc 5
  ζ := S.X (Fin.last r) 1
  ζi := S.X (Fin.last r) 2
  ζb := S.X (Fin.last r) 4
  ζbi := S.X (Fin.last r) 5
  GG := S.gG
  GGi := S.gGi
  nab := S.nab
  nabs := S.nabs
  TT := ((S.T * S.T' : ℝ) : ℂ)
  fns_comm := fun x hx y hy => by
    obtain ⟨f, hf, rfl⟩ := S.isFn_of_mem hx
    obtain ⟨g, hg, rfl⟩ := S.isFn_of_mem hy
    exact fn_comm hf hg
  c_ci := fun l => S.coord_mul_inv_coord_eq_one _
  ci_c := fun l => S.inv_coord_mul_coord_eq_one _
  cb_cbi := fun l => S.conj_coord_mul_conj_inv_eq_one _
  cbi_cb := fun l => S.conj_inv_mul_conj_coord_eq_one _
  ζ_ζi := S.coord_mul_inv_coord_eq_one _
  ζi_ζ := S.inv_coord_mul_coord_eq_one _
  ζb_ζbi := S.conj_coord_mul_conj_inv_eq_one _
  ζbi_ζb := S.conj_inv_mul_conj_coord_eq_one _
  GG_GGi := S.gG_gGi
  GGi_GG := S.gGi_gG
  GG_def := S.gG_def
  p_c := fun l m => by simpa [Fin.castSucc_inj] using S.momentum_coord_commutator l.castSucc m.castSucc
  p_ci := fun l m => by simpa [Fin.castSucc_inj] using S.momentum_inv_coord_commutator l.castSucc m.castSucc
  p_cb := fun l m => S.momentum_commute_conj_coord _ _
  p_cbi := fun l m => S.momentum_commute_conj_inv_coord _ _
  p_ζ := fun l => by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)
  p_ζi := fun l => by simpa [ne_last l] using S.momentum_inv_coord_commutator l.castSucc (Fin.last r)
  p_ζb := fun l => S.momentum_commute_conj_coord _ _
  p_ζbi := fun l => S.momentum_commute_conj_inv_coord _ _
  p_GG := fun l => by
    have := S.der_gG (d := S.P l.castSucc) (a := 0) (b := 0)
      (by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)) (by simpa using S.momentum_commute_conj_coord l.castSucc (Fin.last r))
    simpa using this
  p_GGi := fun l => by
    have := S.der_gGi (d := S.P l.castSucc) (a := 0) (b := 0)
      (by simpa [ne_last l] using S.momentum_coord_commutator l.castSucc (Fin.last r)) (by simpa using S.momentum_commute_conj_coord l.castSucc (Fin.last r))
    simpa using this
  pb_cb := fun l m => by simpa [Fin.castSucc_inj] using S.conj_momentum_conj_coord_commutator l.castSucc m.castSucc
  pb_cbi := fun l m => by simpa [Fin.castSucc_inj] using S.conj_momentum_conj_inv_commutator l.castSucc m.castSucc
  pb_c := fun l m => S.conj_momentum_commute_coord _ _
  pb_ci := fun l m => S.conj_momentum_commute_inv_coord _ _
  pb_ζ := fun l => S.conj_momentum_commute_coord _ _
  pb_ζi := fun l => S.conj_momentum_commute_inv_coord _ _
  pb_ζb := fun l => by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r)
  pb_ζbi := fun l => by simpa [ne_last l] using S.conj_momentum_conj_inv_commutator l.castSucc (Fin.last r)
  pb_GG := fun l => by
    have := S.der_gG (d := S.Pb l.castSucc) (a := 0) (b := 0)
      (by simpa using S.conj_momentum_commute_coord l.castSucc (Fin.last r)) (by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r))
    simpa using this
  pb_GGi := fun l => by
    have := S.der_gGi (d := S.Pb l.castSucc) (a := 0) (b := 0)
      (by simpa using S.conj_momentum_commute_coord l.castSucc (Fin.last r)) (by simpa [ne_last l] using S.conj_momentum_conj_coord_commutator l.castSucc (Fin.last r))
    simpa using this
  p_p := fun l m => S.P_P _ _
  p_pb := fun l m => S.P_Pb _ _
  pb_pb := fun l m => S.Pb_Pb _ _
  p_nab := fun l => ((S.euler_commute_holo_deriv_of_ne (ne_last l)).add_right (S.euler_commute_mul_of_fderiv_eq_zero S.h_sm S.h_c l)).eq
  pb_nab := fun l => ((S.Pb_dW _ _).add_right (S.Pb_fe S.h_sm S.h_c l)).eq
  p_nabs := fun l => ((S.euler_commute_antiholo_deriv _ _).neg_right.add_right (S.euler_commute_mul_of_fderiv_eq_zero S.hs_sm S.hs_c l)).eq
  pb_nabs := fun l => ((S.Pb_dWb (ne_last l)).neg_right.add_right (S.Pb_fe S.hs_sm S.hs_c l)).eq
  nab_ζ := by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r))
  nab_ζi := by
    have := S.holo_deriv_inv_coord_commutator (Fin.last r) (Fin.last r)
    rw [sub_eq_add_neg] at this
    simpa [sub_eq_add_neg] using S.nab_X this
  nab_ζb := by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r))
  nab_ζbi := by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_inv_coord (Fin.last r) (Fin.last r))
  nab_GG := by
    have := S.der_gG (d := S.nab) (a := 1) (b := 0)
      (by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r)))
      (by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r)))
    simpa using this
  nab_GGi := by
    have := S.der_gGi (d := S.nab) (a := 1) (b := 0)
      (by simpa using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) (Fin.last r)))
      (by simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) (Fin.last r)))
    rw [this]
    simp only [one_mul, mul_zero, add_zero]
    rw [show S.gGi * S.X (Fin.last r) 4 = S.X (Fin.last r) 4 * S.gGi from fn_comm S.hGGi (S.hc _ 4)]
  nab_c := fun l => by
    simpa [last_ne l] using S.nab_X (S.holo_deriv_coord_commutator (Fin.last r) l.castSucc)
  nab_ci := fun l => by
    have := S.holo_deriv_inv_coord_commutator (Fin.last r) l.castSucc
    rw [sub_eq_add_neg] at this
    simpa [last_ne l] using S.nab_X this
  nab_cb := fun l => by
    simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_coord (Fin.last r) l.castSucc)
  nab_cbi := fun l => by
    simpa using S.nab_X (K := 0) (by simpa using S.holo_deriv_commute_conj_inv_coord (Fin.last r) l.castSucc)
  nabs_ζb := by simpa using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r))
  nabs_ζbi := by
    have := S.antiholo_deriv_conj_inv_commutator (Fin.last r) (Fin.last r)
    rw [sub_eq_add_neg] at this
    simpa [sub_eq_add_neg] using S.nabs_X this
  nabs_ζ := by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r))
  nabs_ζi := by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_inv_coord (Fin.last r) (Fin.last r))
  nabs_GG := by
    have := S.der_gG (d := S.nabs) (a := 0) (b := -1)
      (by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r)))
      (by simpa [sub_eq_add_neg] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r)))
    simpa [sub_eq_add_neg] using this
  nabs_GGi := by
    have := S.der_gGi (d := S.nabs) (a := 0) (b := -1)
      (by simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) (Fin.last r)))
      (by simpa [sub_eq_add_neg] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) (Fin.last r)))
    rw [this]
    simp only [zero_mul, zero_add, mul_neg, mul_one, neg_mul, sub_neg_eq_add]
    rw [show S.gGi * S.X (Fin.last r) 1 = S.X (Fin.last r) 1 * S.gGi from fn_comm S.hGGi (S.hc _ 1)]
  nabs_c := fun l => by
    simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_coord (Fin.last r) l.castSucc)
  nabs_ci := fun l => by
    simpa using S.nabs_X (K := 0) (by simpa using S.antiholo_deriv_commute_inv_coord (Fin.last r) l.castSucc)
  nabs_cb := fun l => by
    simpa [last_ne l] using S.nabs_X (S.antiholo_deriv_conj_coord_commutator (Fin.last r) l.castSucc)
  nabs_cbi := fun l => by
    have := S.antiholo_deriv_conj_inv_commutator (Fin.last r) l.castSucc
    rw [sub_eq_add_neg] at this
    simpa [last_ne l] using S.nabs_X this

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WirtingerDerivatives Formalism.MainNotions.S.LevR

section RepSec

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}

def Rep (U : Set (Fin m → ℂ)) (O : Op m E) (a : Module.End ℂ (SmU U E)) : Prop :=
  ∀ (φ : (Fin m → ℂ) → E) (μ : SmU U E), (∀ x ∈ U, φ x = μ.1 x) → ∀ x ∈ U, O φ x = (a μ).1 x

theorem Rep.comp {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O ∘ O') (a * a') := fun φ μ e x hx => h (O' φ) (a' μ) (h' φ μ e) x hx

theorem Rep.add {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O + O') (a + a') := fun φ μ e x hx => by
  simp only [Pi.add_apply, LinearMap.add_apply, Submodule.coe_add, h φ μ e x hx, h' φ μ e x hx]

theorem Rep.sub {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a') :
    Rep U (O - O') (a - a') := fun φ μ e x hx => by
  simp only [Pi.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, h φ μ e x hx, h' φ μ e x hx]

theorem Rep.neg {O : Op m E} {a : Module.End ℂ (SmU U E)} (h : Rep U O a) :
    Rep U (-O) (-a) := fun φ μ e x hx => by
  simp only [Pi.neg_apply, LinearMap.neg_apply, Submodule.coe_neg, h φ μ e x hx]

theorem Rep.zero : Rep U (0 : Op m E) 0 := fun φ μ _ x _ => by simp

theorem Rep.one : Rep U (one : Op m E) 1 := fun φ μ e x hx => e x hx

theorem Rep.cast {O : Op m E} {a b : Module.End ℂ (SmU U E)} (h : Rep U O a) (e : a = b) : Rep U O b := e ▸ h

theorem Rep.eq {O O' : Op m E} {a a' : Module.End ℂ (SmU U E)} (h : Rep U O a) (h' : Rep U O' a')
    (e : a = a') {φ : (Fin m → ℂ) → E} (hφ : ContDiffOn ℝ ∞ φ U) {x : Fin m → ℂ} (hx : x ∈ U) :
    O φ x = O' φ x := by
  classical
  let μ : SmU U E := ⟨U.indicator φ, hφ.congr (fun y hy => Set.indicator_of_mem hy _),
    fun y hy => Set.indicator_of_notMem hy _⟩
  have hμ : ∀ y ∈ U, φ y = μ.1 y := fun y hy => (Set.indicator_of_mem hy _).symm
  rw [h φ μ hμ x hx, h' φ μ hμ x hx, e]

def IsMul (a : Module.End ℂ (SmU U E)) (f : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ (μ : SmU U E), ∀ x ∈ U, (a μ).1 x = f x • μ.1 x

theorem IsMul.mul {a b : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f) (hb : IsMul b g) :
    IsMul (a * b) (fun x => f x * g x) := fun μ x hx => by
  rw [Module.End.mul_apply, ha _ x hx, hb _ x hx, mul_smul]

theorem IsMul.one : IsMul (U := U) (E := E) 1 (fun _ => 1) := fun μ x _ => by simp

theorem IsMul.prod : ∀ (n : ℕ) (a : Fin n → Module.End ℂ (SmU U E)) (f : Fin n → (Fin m → ℂ) → ℂ),
    (∀ i, IsMul (a i) (f i)) → IsMul (List.ofFn a).prod (fun x => ∏ i, f i x)
  | 0, _, _, _ => by simpa using IsMul.one
  | n + 1, a, f, h => by
    rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.prod_univ_succ]
    exact (h 0).mul (IsMul.prod n _ _ (fun i => h i.succ))

theorem IsMul.ext {a b : Module.End ℂ (SmU U E)} {f g : (Fin m → ℂ) → ℂ} (ha : IsMul a f) (hb : IsMul b g)
    (e : ∀ x ∈ U, f x = g x) : a = b :=
  end_ext fun μ x hx => by rw [ha μ x hx, hb μ x hx, e x hx]

end RepSec

namespace Setup

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

namespace Setup

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

namespace Setup

end Setup

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

namespace RulesHyp

end RulesHyp

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

end Formalism.MainNotions.LevelRaisingOperators

namespace Formalism.MainNotions.LevelRaisingOperators

end Formalism.MainNotions.LevelRaisingOperators
