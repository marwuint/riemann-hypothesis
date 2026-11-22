import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelZeroLogConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LineNorm

section Closure

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Good (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) : Prop :=
  (∀ y, Δ.IsEqn y (t y)) ∧ FromModel Y Δ t φ

theorem Good.congr {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y} (h : Good Y Δ t φ) (h₁ : Δ = Δ')
    (h₂ : ∀ y, t y = t' y) (h₃ : ∀ v e y, φ v e y = φ' v e y) : Good Y Δ' t' φ' := by
  obtain rfl : t = t' := funext h₂
  obtain rfl : φ = φ' := funext fun v => funext fun e => funext (h₃ v e)
  exact h₁ ▸ h

theorem Good.add {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y} (h : Good Y Δ t φ) (h' : Good Y Δ' t' φ') :
    Good Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) :=
  ⟨fun y => (h.1 y).add (h'.1 y), GlobalTheory.T.fromModel_add' F Y _ _ _ _ _ _ h.1 h'.1 h.2 h'.2⟩

theorem Good.neg {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) :
    Good Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) :=
  ⟨fun y => (h.1 y).neg, GlobalTheory.T.fromModel_neg' F Y _ _ _ h.1 h.2⟩

theorem good_const (a : F) (n : ℕ) (ha : a ≠ 0) (hn : n ≠ 0) :
    Good Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) :=
  ⟨fun y => CartierDiv.isEqn_zero y, _root_.GlobalTheory.LineNorm.fromModel_const F Y a n ha hn⟩

theorem good_zero : Good Y 0 (fun _ => 1) (fun _ _ _ => 0) :=
  (good_const 1 1 one_ne_zero one_ne_zero).congr rfl (fun _ => rfl) (fun _ _ _ => by simp)

omit [NumberField F] in
theorem isEqn_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.Fnˣ} (y : Y.X)
    (h : ∀ a, (Δ a).IsEqn y (t a)) : (∑ a ∈ s, Δ a).IsEqn y (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a).add ih

theorem good_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.X → Y.Fnˣ} {φ : α → PtFn Y}
    (h : ∀ a ∈ s, Good Y (Δ a) (t a) (φ a)) :
    Good Y (∑ a ∈ s, Δ a) (fun y => ∏ a ∈ s, t a y) (fun v e y => ∑ a ∈ s, φ a v e y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    refine ((h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))).congr
      (Finset.sum_insert ha).symm (fun _ => by rw [Finset.prod_insert ha]) (fun _ _ _ => by rw [Finset.sum_insert ha])

theorem Good.nsmul {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) (n : ℕ) :
    Good Y (n • Δ) (fun y => t y ^ n) (fun v e y => (n : ℝ) * φ v e y) :=
  (good_sum (Finset.range n) (fun _ _ => h)).congr (by simp) (by simp) (by simp)

theorem Good.zsmul {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) (n : ℤ) :
    Good Y (n • Δ) (fun y => t y ^ n) (fun v e y => (n : ℝ) * φ v e y) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (h.nsmul m).congr (by simp) (by simp) (by simp)
  · exact (h.nsmul m).neg.congr (by simp) (by simp) (by simp)

theorem Good.change {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y} (h : Good Y Δ t φ) {t' : Y.X → Y.Fnˣ}
    (h' : ∀ y, Δ.IsEqn y (t' y)) :
    FromModel Y Δ t' (fun v e y =>
      Real.log (e.w (valAt y.1 ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) + φ v e y) := by
  obtain ⟨h₁, M, L, m, r, hL, hP, hv⟩ := h
  refine ⟨M, L, m, r, hL, hP, fun v e y yt i hy hU => ?_⟩
  have hmem : below y.1 ∈ (L.pull M.j).U i := by
    have h2 : ∀ U : M.X.Opens, ⊤ ≤ yt ⁻¹ᵁ U → M.j (below y.1) ∈ U := fun U hU => by
      have e₀ : M.j (below y.1) = yt (spMap e.O.subtype (IsLocalRing.closedPoint _)) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun q : Sp (AlgebraicClosure F) ⟶ M.X => q (IsLocalRing.closedPoint _)) hy.symm).trans (Scheme.Hom.comp_apply _ _ _))
      exact e₀ ▸ hU (Set.mem_univ _)
    exact Set.mem_iInter.2 fun _ => h2 _ hU
  have u₁ : UnitAt (below y.1) ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) := by
    simpa [div_eq_mul_inv] using (h' (below y.1)).iff_unitAt.1 (h₁ _)
  have u₂ : UnitAt (below y.1) (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
    simpa [div_eq_mul_inv, mul_comm] using ((h₁ (below y.1)).nsmul m).iff_unitAt.1 (hP.isEqn i _ hmem)
  have e₁ : (((t' (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) =
      ((t (below y.1) * (t' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) ^ (m : ℕ) *
        (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [mul_pow, mul_comm (t _ ^ _), mul_assoc, ← mul_assoc (t _ ^ _), ← mul_pow, mul_inv_cancel, one_pow, one_mul]
  have n₁ := SmallSec.valAt_ne_zero u₁
  have n₂ := SmallSec.valAt_ne_zero u₂
  rw [e₁, SmallSec.valAt_mul (SmallSec.regAt_pow u₁.regAt _) u₂.regAt, SmallSec.valAt_pow u₁.regAt, map_mul, map_pow,
    Real.log_mul (pow_ne_zero _ (e.w.ne_zero n₁)) (e.w.ne_zero n₂), Real.log_pow, mul_add, hv v e y yt i hy hU]

end Closure

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem good_step (hB : HTBoundSt) [IsLocallyNoetherian X] (hX : X.IsSeparated) (M : GlobalTheory.TrueGeo.Model Y)
    (ρ' : M.X ⟶ X) {ρ : Y.X ⟶ X} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (hρ : M.j ≫ ρ' = ρ) {m : ℕ}
    {u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)}
    {f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {d : Y.X → Fin m → Y.Fnˣ}
    (h : IsFlagFrame t ρ u₀ f d) {Δ : Fin m → Y.Dv} (hΔ : ∀ y i, (Δ i).IsEqn y (d y i)) (q : ℕ) (i : Fin m) :
    Good Y (Δ i) (fun y => d y i) (stepLog t ρ f q i) := by
  have key : ∀ (k : ℕ) (hk : k ≤ m), Good Y (∑ l : Fin k, Δ (Fin.castLE hk l))
      (fun y => ∏ l : Fin k, d y (Fin.castLE hk l))
      (fun v e y => ∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) := fun k hk => by
    have he : ∀ y, (∑ l : Fin k, Δ (Fin.castLE hk l)).IsEqn y (∏ l : Fin k, d y (Fin.castLE hk l)) := fun y =>
      isEqn_sum _ y fun l => hΔ y _
    exact ⟨he, _root_.GlobalTheory.LineNorm.Glue.fromModel_of_locMax F Y M _ _ _ he (_root_.GlobalTheory.LineNorm.Chart.locMax_flag hB E H X t hX F Y M ρ' ρ hM hρ m u₀ f d h q k hk)⟩
  have hi : Fin.castLE (Nat.succ_le_of_lt i.2) (Fin.last i) = i := rfl
  refine ((key (i + 1) i.2).add (key i i.2.le).neg).congr ?_ (fun y => ?_) (fun v e y => ?_)
  · rw [Fin.sum_univ_castSucc, hi]
    exact add_neg_cancel_comm _ _
  · rw [Fin.prod_univ_castSucc, hi]
    exact mul_inv_cancel_comm _ _
  · rw [Fin.sum_univ_castSucc, hi]
    exact add_neg_cancel_comm _ _

variable (t) in
open Classical in

def mixLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (b : ℕ → Bool) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (b (resP v)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

end Steps

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

abbrev fr (y : C.Y.X) := (C.gr_spec y).choose_spec.choose

abbrev dg (y : C.Y.X) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ := (C.gr_spec y).choose_spec.choose_spec.choose

omit [NumberField F] in
theorem fr_spec (y : C.Y.X) : (fr C y).Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (dg C y) ∧
    ∀ τ i, (C.gr τ i).IsEqn y (dg C y τ i) := (C.gr_spec y).choose_spec.choose_spec.choose_spec

omit [NumberField F] in
theorem isFrame_fr (y : C.Y.X) {k : Type} [CommRing k] (ψ : C.Y.X.presheaf.stalk y →+* k) :
    GlobalTheory.LocM.IsFrame Z.t (ψ.comp (C.gr_spec y).choose) (spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z)
      (Vecs.bc ψ (fr C y).v) :=
  _root_.GlobalTheory.ShFam.Pad.isFrame_baseChange E H Dw l c Z.X Z.t _ k _ ψ _ (fr C y).v
    ⟨fun τ i => ⟨(fr C y).tan τ i, (fr C y).eig τ i⟩, (fr C y).basis⟩

attribute [local instance] Over.cartesianMonoidalCategory in
omit [NumberField F] in
theorem sum_expo {G : Type} [AddCommGroup G] (g : Letter Dw → G) (w : Sym E →₀ ℤ) :
    ∑ a ∈ w.support, w a • ((letterOf Dw a.2.2).elim 0 g) = ∑ x, expo Dw w x • g x := by
  classical
  simp only [expo, Finsupp.sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases letterOf Dw a.2.2 <;> simp

end Flags

end GlobalTheory.LineNorm
