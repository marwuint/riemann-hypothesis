import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bor (a d : kˣ) (x : k) : GL (Fin (1 + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : k), x; 0, (d : k)] (by simp)

def nU (x : k) : GL (Fin (1 + 1)) k := bor 1 1 x

def nL (x : k) : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp)

def wE : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)

def tD (a d : kˣ) : GL (Fin (1 + 1)) k := bor a d 0

@[simp] theorem val_bor (a d : kˣ) (x : k) :
    ((bor a d x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), x; 0, (d : k)] := rfl

@[simp] theorem val_nL (x : k) :
    ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, 0; x, 1] := rfl

@[simp] theorem val_wE :
    ((wE : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![0, 1; 1, 0] := rfl

@[simp] theorem val_nU (x : k) :
    ((nU x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, x; 0, 1] := by
  simp [nU]

@[simp] theorem val_tD (a d : kˣ) :
    ((tD a d : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), 0; 0, (d : k)] := by
  simp [tD]

abbrev PSp (μ₁ μ₂ : kˣ →* ℂˣ) : Type :=
  IndSp (two (stdSum (rfl : 1 + 1 = 1 + 1)))
    ((extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)).comp (leviTwo k (Fin 1) (Fin 1)).symm.toMonoidHom)

abbrev psRep (μ₁ μ₂ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin (1 + 1)) k) (PSp μ₁ μ₂) :=
  prod₂ (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)

def ev {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) : ℂ := TensorProduct.lid ℂ ℂ (f.1.1 g)

def coord {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (x : k) : ℂ := ev f (wE * nU x)

def bchar (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : ℂ :=
  ((μ₁ a * μ₂ d * absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ)

theorem ev_add {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f + f') g = ev f g + ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g + f'.1.1 g) = _
  rw [map_add]; rfl

theorem ev_smul {μ₁ μ₂ : kˣ →* ℂˣ} (c : ℂ) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (c • f) g = c * ev f g := by
  show TensorProduct.lid ℂ ℂ (c • f.1.1 g) = _
  rw [map_smul]; rfl

theorem ev_act {μ₁ μ₂ : kˣ →* ℂˣ} (h : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (psRep μ₁ μ₂ h f) g = ev f (g * h) := rfl

def evL (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) : PSp μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun f := ev f g
  map_add' f f' := ev_add f f' g
  map_smul' c f := ev_smul c f g

def coordL (μ₁ μ₂ : kˣ →* ℂˣ) : PSp μ₁ μ₂ →ₗ[ℂ] (k → ℂ) where
  toFun f := coord f
  map_add' f f' := funext fun x => ev_add f f' _
  map_smul' c f := funext fun x => ev_smul c f _

@[simp] theorem evL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) :
    evL μ₁ μ₂ g f = ev f g := rfl

@[simp] theorem coordL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) : coordL μ₁ μ₂ f = coord f := rfl

@[simp] theorem bchar_one (μ₁ μ₂ : kˣ →* ℂˣ) : bchar μ₁ μ₂ 1 1 = 1 := by simp [bchar]

def ball (c : k) (r : kˣ) : Set k := {z | valuation k (z - c) ≤ valuation k (r : k)}

def elemDiff (c c' : k) (r : kˣ) : k → ℂ := (ball c r).indicator 1 - (ball c' r).indicator 1

end GlobalTheory.PrinTwo
