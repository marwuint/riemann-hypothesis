import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCW

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab Formalism.BasicNotions.Examples₂

variable {D : D7}

theorem xs_fits (R : Ranks) (t j : ℕ) (hj : j < R.m) : R.k + j * (t + 1) ≤ R.r + j * t - (R.m - j) / 2 := by
  have h1 : j * (t + 1) = j * t + j := by ring
  rw [h1]
  generalize j * t = s
  unfold Ranks.r
  omega

theorem nu_le (R : Ranks) (t j : ℕ) : (R.m - j) / 2 ≤ R.r + j * t := by
  have hk := R.m_add_three_le_k
  have : (R.m - j) / 2 ≤ R.r := by unfold Ranks.r; omega
  omega

def sigTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => dSpace star_isIntegral (D.R.r + j * t) ((D.R.m - j) / 2)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun j _ => dSpace_sigOK _ _ _ (nu_le D.R t j)
  iXYs := fun _ => extLE _ _
  iXYs_isom := fun j hj x y => extLE_isom _ _ ((xs_fits D.R t j hj).trans (Nat.sub_le _ _)) _ _
    (fun i => negTail_false _ _ _ (lt_of_lt_of_le i.isLt (xs_fits D.R t j hj))) x y
  iYXm := extLE _ _
  iYXm_isom := fun x y => extLE_isom _ _ (by
      have := D.R.two_le_m
      unfold Ranks.r
      rw [Nat.mul_succ]
      omega) _ _ (fun i => (negTail_false _ _ _ (by have := i.isLt; omega)).symm) x y

open Classical in

def towC (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else sigTow D t

def SpSig (D : D7) : Prop :=
  ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef ∧
    ∀ τ, (D.sp.Y j).sig τ = (D.R.r + j * D.R.t - (D.R.m - j) / 2, (D.R.m - j) / 2)

open Classical in

def lowC (V : HSp D) (i : ℕ) : HSp D :=
  if i = 0 then V else if h : ∃ V' : HSp D, IsWittLower V V' i then fixSig h.choose else V

def EmbU (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ g g' h, EmbRel A B ι g h → EmbRel A B ι g' h → g = g'

def EmbRat (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ γ ∈ GQ B, ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ

def TopInt (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
  ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ (s h)) * F h) 𝓕 μ

section Bessel

variable (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def NPair (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) p.2 p.1 ∧ p.1 p.2 = 1

def besIn (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (F : GA D B → ℂ) (x : GA D B) : ℂ :=
  ∫ n in p.2, F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B)) ∂p.1

end Bessel

def BesInt1 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p, NPair d p → ∀ F : GA D B → ℂ, IsAutFun B F → ∀ x,
    IntegrableOn (fun n : NFlag B d.e => F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B))) p.2 p.1

def BesInv (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p p', NPair d p → NPair d p' → ∀ F : GA D B → ℂ, IsAutFun B F →
    ∀ γ' ∈ GQ B, ∀ γ : GA D A, EmbRel B A ι γ' γ → ∀ x, besIn ψ d p F (γ' * x) = besIn ψ d p' F x

def BesInt2 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  HSpace.IsIsomEmb A B ι → ∀ p, NPair d p → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
  ∀ (μ : Measure (GA D A)) (𝓕 : Set (GA D A)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsCuspFun A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ h) * besIn ψ d p F (s h * (d.y : GA D B))) 𝓕 μ

structure PerGaps (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  embU : EmbU D
  embRat : EmbRat D
  topInt : TopInt D
  int1 : BesInt1 ψ
  inv : BesInv ψ
  int2 : BesInt2 ψ

end Formalism.L2.Fam.ThC

end
