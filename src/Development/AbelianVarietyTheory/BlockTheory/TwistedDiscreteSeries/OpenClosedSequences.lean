import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

def sbRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : ∀ g, Continuous fun x => r x g) :
    Representation ℂ Γ (SB X) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (r x g), f.2.1.comp_continuous (hc g),
        f.2.2.comp_homeomorph
          { toFun := fun x => r x g
            invFun := fun x => r x g⁻¹
            left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc g
            continuous_invFun := hc g⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (h1 x))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (hm x g h))

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n Γ W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Group Γ] [AddCommGroup W] [Module ℂ W]

def actFst (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ) :
    Representation.IntertwiningMap
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom) where
  toLinearMap := τ (γ, 1)
  isIntertwining' m := by
    show τ (γ, 1) * τ (1, _) = τ (1, _) * τ (γ, 1)
    rw [← map_mul, ← map_mul]
    simp

def indSnd (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) :
    Representation ℂ (Γ × GL n k)
      (IndSp (two e) (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)) where
  toFun g := (parIndMap (two e) (actFst τ g.1)).toLinearMap ∘ₗ ind₂ e (τ.comp (MonoidHom.inr Γ _)) g.2
  map_one' := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * 1)) = f.1.1 x
    simp))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (g.1 * h.1, 1) (f.1.1 (x * (g.2 * h.2))) = τ (g.1, 1) (τ (h.1, 1) (f.1.1 (x * g.2 * h.2)))
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc]
    simp))

theorem indSnd_apply (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ)
    (h x : GL n k) (f) : (indSnd e τ (γ, h) f).1.1 x = τ (γ, 1) (f.1.1 (x * h)) := rfl

theorem indSnd_inr (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (h : GL n k) :
    indSnd e τ (1, h) = ind₂ e (τ.comp (MonoidHom.inr Γ _)) h :=
  LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * h)) = f.1.1 (x * h)
    simp))

end Ind

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def act (x : Matrix b a k) (γ : GL a k × GL b k) : Matrix b a k := (γ.2⁻¹ : GL b k).val * x * γ.1.val

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_one (x : Matrix b a k) : act x 1 = x := by simp [act]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_mul (x : Matrix b a k) (γ δ : GL a k × GL b k) : act x (γ * δ) = act (act x γ) δ := by
  simp only [act, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem continuous_act (γ : GL a k × GL b k) : Continuous fun x : Matrix b a k => act x γ :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rank_act (x : Matrix b a k) (γ : GL a k × GL b k) : (act x γ).rank = x.rank := by
  unfold act
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 γ.1.isUnit),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (γ.2⁻¹).isUnit)]

variable (a b)

def omChar (μ : kˣ →* ℂˣ) : GL a k × GL b k →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2))).comp (MonoidHom.fst _ _) *
    (detChar b (μ * absPow k (-(Fintype.card a : ℂ) / 2))).comp (MonoidHom.snd _ _)

def omega (μ : kˣ →* ℂˣ) : Representation ℂ (GL a k × GL b k) (SB (Matrix b a k)) :=
  twist (sbRep act act_one act_mul continuous_act) (omChar a b μ)

variable (k) in

abbrev RankIn (s : Set ℕ) : Type := {x : Matrix b a k // x.rank ∈ s}

def omegaOn (μ : kˣ →* ℂˣ) (s : Set ℕ) : Representation ℂ (GL a k × GL b k) (SB (RankIn k a b s)) :=
  twist (sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)) (omChar a b μ)

variable {a b}

theorem omegaOn_apply (μ : kˣ →* ℂˣ) (s : Set ℕ) (γ : GL a k × GL b k) (Φ : SB (RankIn k a b s))
    (x : RankIn k a b s) :
    (omegaOn a b μ s γ Φ).1 x =
      (omChar a b μ γ : ℂ) * Φ.1 ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩ := rfl

variable (a b) in

def filt (μ : kˣ →* ℂˣ) (s : Set ℕ) (κ : ℕ) : Subrepresentation (omegaOn a b μ s) where
  toSubmodule :=
    { carrier := {Φ | ∀ x : RankIn k a b s, x.1.rank < κ → Φ.1 x = 0}
      add_mem' := fun {f g} hf hg x hx => by
        show f.1 x + g.1 x = 0
        rw [hf x hx, hg x hx, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c f hf x hx => by
        show c * f.1 x = 0
        rw [hf x hx, mul_zero] }
  apply_mem_toSubmodule γ Φ hΦ x hx := by
    rw [omegaOn_apply, hΦ _ (by rwa [rank_act]), mul_zero]

end Model

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
