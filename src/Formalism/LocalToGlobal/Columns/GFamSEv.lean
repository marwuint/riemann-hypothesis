import Mathlib
import Formalism.LocalToGlobal.Columns.GFamEv
import Formalism.LocalToGlobal.Columns.GFamSH

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev Pt (F : GFamS K) : Type := Σ b, F.D b

def cls (F : GFamS K) (p : F.Pt) : F.Cl := ⟨p.1, (F.mem p.1).cls p.2⟩

def repPt (F : GFamS K) (c : F.Cl) : F.Pt := ⟨c.1, F.rep c⟩

structure Ev (F : GFamS K) (σ : K →+* ℂ) where

  Y : Type

  ev : F.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (F.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (F.pair x y)

  tr : ∀ b, F.G b →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ b g x, tr b g (ev x) = ev (F.ρ b g x)

namespace Ev

variable {F : GFamS K} {σ : K →+* ℂ} (E : F.Ev σ)

@[reducible] def mem (b : F.β) : (F.mem b).Ev σ where
  Y := E.Y
  ev := E.ev
  li := E.li
  ip := E.ip
  ip_ev := E.ip_ev
  tr := E.tr b
  tr_ev := E.tr_ev b

theorem mem_Y (b : F.β) : (E.mem b).Y = E.Y := rfl
theorem mem_ev (b : F.β) : (E.mem b).ev = E.ev := rfl
theorem mem_ip (b : F.β) : (E.mem b).ip = E.ip := rfl
theorem mem_tr (b : F.β) : (E.mem b).tr = E.tr b := rfl

@[reducible] def ofMem {b₀ : F.β} (E₀ : (F.mem b₀).Ev σ) (tr : ∀ b, F.G b →* ((E₀.Y → ℂ) ≃ₗ[ℂ] (E₀.Y → ℂ)))
    (tr_ev : ∀ b g x, tr b g (E₀.ev x) = E₀.ev (F.ρ b g x)) : F.Ev σ where
  Y := E₀.Y
  ev := E₀.ev
  li := E₀.li
  ip := E₀.ip
  ip_ev := E₀.ip_ev
  tr := tr
  tr_ev := tr_ev

def emb : F.Forms →ₛₗ[σ] (F.Cl → E.Y → ℂ) where
  toFun φ := fun c => E.ev (F.valAt φ c)
  map_add' φ ψ := by funext c; exact map_add E.ev _ _
  map_smul' a φ := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

theorem emb_apply (φ : F.Forms) (c : F.Cl) :
    E.emb φ c = E.ev (((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) ((F.sec c.1).rep c.2)) := rfl

theorem emb_valAt (φ : F.Forms) (c : F.Cl) : E.emb φ c = E.ev (F.valAt φ c) := rfl

def part (b : F.β) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] ((F.mem b).Cl → E.Y → ℂ) :=
  LinearMap.pi fun c => LinearMap.proj (⟨b, c⟩ : F.Cl)

theorem part_apply (b : F.β) (Φ : F.Cl → E.Y → ℂ) (c : (F.mem b).Cl) : E.part b Φ c = Φ ⟨b, c⟩ := rfl

def trPt (p : F.Pt) : (E.Y → ℂ) ≃ₗ[ℂ] (E.Y → ℂ) := E.tr p.1 ((F.sec p.1).mv p.2)

def atPt (p : F.Pt) (Φ : F.Cl → E.Y → ℂ) : E.Y → ℂ := E.trPt p (Φ (F.cls p))

def opOn (δ : F.Pt → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) where
  toFun Φ := fun c => E.atPt (δ (F.repPt c)) Φ
  map_add' Φ Ψ := by funext c; exact map_add (E.trPt _) _ _
  map_smul' a Φ := by funext c; exact map_smul (E.trPt _) _ _

theorem opOn_apply (δ : F.Pt → F.Pt) (Φ : F.Cl → E.Y → ℂ) (c : F.Cl) :
    E.opOn δ Φ c = E.trPt (δ (F.repPt c)) (Φ (F.cls (δ (F.repPt c)))) := rfl

def opOnC (δ : ∀ b, F.D b → F.D b) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) := E.opOn fun p => ⟨p.1, δ p.1 p.2⟩

theorem opOnC_apply (δ : ∀ b, F.D b → F.D b) (Φ : F.Cl → E.Y → ℂ) (c : F.Cl) :
    E.opOnC δ Φ c = E.trPt ⟨c.1, δ c.1 (F.rep c)⟩ (Φ ⟨c.1, (F.mem c.1).cls (δ c.1 (F.rep c))⟩) := rfl

def lin : (F.ιV → ℂ) →ₗ[ℂ] (E.Y → ℂ) := Fintype.linearCombination ℂ fun i => E.ev (F.bV i)

theorem lin_ker : LinearMap.ker E.lin = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact E.li.fintypeLinearCombination_injective

def gram : Matrix F.ιV F.ιV ℂ := Matrix.of fun i j => E.ip (E.ev (F.bV i)) (E.ev (F.bV j))

def ipB : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) := LinearMap.pi fun j => E.ip (E.ev (F.bV j))

open Classical in

def co : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) :=
  if IsUnit E.gram.det then Matrix.toLin' E.gram⁻¹ ∘ₗ E.ipB
  else (E.lin.exists_leftInverse_of_injective E.lin_ker).choose

def extend {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) : (E.Y → ℂ) →ₗ[ℂ] M :=
  (Fintype.linearCombination ℂ fun i => ℓ (F.bV i)) ∘ₗ E.co

def sharp (ℓ : F.V →ₛₗ[σ] ℂ) : E.Y → ℂ :=
  ∑ j, starRingEnd ℂ (∑ i, ℓ (F.bV i) * E.gram⁻¹ i j) • E.ev (F.bV j)

theorem lin_mem (b : F.β) : (E.mem b).lin = E.lin := rfl
theorem gram_mem (b : F.β) : (E.mem b).gram = E.gram := rfl
theorem ipB_mem (b : F.β) : (E.mem b).ipB = E.ipB := rfl
theorem co_mem (b : F.β) : (E.mem b).co = E.co := rfl
theorem extend_mem (b : F.β) {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) :
    (E.mem b).extend ℓ = E.extend ℓ := rfl
theorem sharp_mem (b : F.β) (ℓ : F.V →ₛₗ[σ] ℂ) : (E.mem b).sharp ℓ = E.sharp ℓ := rfl

def Fi : Submodule ℂ (F.Cl → E.Y → ℂ) := Submodule.span ℂ (Set.range E.emb)

def evAt {ι : Type} (pts : ι → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → E.Y → ℂ) :=
  LinearMap.pi fun i => (E.trPt (pts i)).toLinearMap ∘ₗ LinearMap.proj (F.cls (pts i))

theorem evAt_apply {ι : Type} (pts : ι → F.Pt) (Φ : F.Cl → E.Y → ℂ) (i : ι) : E.evAt pts Φ i = E.atPt (pts i) Φ := rfl

def perCl (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) :
    (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  LinearMap.mk₂ ℂ (fun Φ z => ∑ c : F.Cl,
      ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * ∑ a, z a * E.extend (ℓ c a) (Φ c))
    (fun Φ Φ' z => by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)
    (fun Φ z z' => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)

theorem perCl_apply (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) (Φ : F.Cl → E.Y → ℂ) (z : ι → ℂ) :
    E.perCl h ℓ Φ z = (letI := h.fintypeCl
      ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ *
        ∑ a, z a * E.extend (ℓ c a) (Φ c)) := rfl

end Ev

end GFamS

end Formalism.L2.Col
