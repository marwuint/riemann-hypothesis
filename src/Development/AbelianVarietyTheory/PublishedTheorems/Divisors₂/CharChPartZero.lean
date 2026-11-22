import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

section Values

variable {n : ℕ}

def hermMat (α : Alt n) : Matrix (Fin n) (Fin n) ℂ :=
  of fun a b => -Complex.I * (bas n).repr α {a.castAdd n, b.natAdd n}

def eval₂ (α : Alt n) (ξ η : V n) : ℂ :=
  Complex.I * (HermFrame.form (hermMat α) ξ η - HermFrame.form (hermMat α) η ξ)

end Values

def chPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ := ((j.factorial : ℚ)⁻¹) • ⟨psum (Fin r) ℚ j, psum_isSymmetric _ _ j⟩

def tdPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ :=
  ⟨homogeneousComponent j (∏ i, ∑ m ∈ Finset.range (j + 1), C (bernoulli' m / m.factorial) * X i ^ m), fun e => by
    rw [rename_homogeneousComponent, map_prod]
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp⟩

def rCoeff (m : ℕ) : ℝ := (2 * deriv riemannZeta (-m) + riemannZeta (-m) * (harmonic m : ℚ)).re

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

namespace ArRing

variable {B : BottChern} {h : IsRegVar p D} (R : ArRing B h) {r : ℕ} (E : HermVB p r)

def char : symmetricSubalgebra (Fin r) ℚ →ₐ[ℚ] R.CH :=
  (aeval fun i : Fin r => R.cl E (i + 1)).comp (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).symm.toAlgHom

def ch : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (chPart r j)

def td : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (tdPart r j)

def rForm : h.Fld :=
  ∑ m ∈ (Finset.range (D + 1)).filter Odd, (rCoeff m : ℂ) • h.coeFld (R.om (R.char E (chPart r m)))

theorem IsPull.char {h' : IsRegVar q D'} {R' : ArRing B h'} {π : Y ⟶ X} {hπ : π ≫ p = q} {f : R.CH →ₐ[ℚ] R'.CH}
    (H : R.IsPull R' π hπ f) (φ : symmetricSubalgebra (Fin r) ℚ) : f (R.char E φ) = R'.char (E.pull π hπ) φ := by
  simp only [ArRing.char, AlgHom.comp_apply, ← H.cl]
  exact comp_aeval_apply _ f _

end ArRing

variable (q) in

def IsGenSmooth (π : Y ⟶ X) : Prop :=
  ∃ U : Y.Opens, (∀ σ (y : CxPts q σ), y ∈ ptsIn q σ U) ∧ Smooth (U.ι ≫ π)

theorem IsGenSmooth.of_smooth (π : Y ⟶ X) [Smooth π] : IsGenSmooth q π :=
  ⟨⊤, fun _ _ => mem_ptsIn_top, inferInstance⟩

def IsRegVar.IsFibreInt (h : IsRegVar p D) (h' : IsRegVar q D') (π : Y ⟶ X) (hπ : π ≫ p = q) (η : h'.Fld) (η' : h.Fld) :
    Prop :=
  ∀ σ j φ, (h.atlas σ).IsRealForm j φ → (h.atlas σ).integral (η' σ * φ) =
    (h'.atlas σ).integral (η σ * (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π hπ _) φ)

structure ArChow.Push {B : BottChern} (C : ArChow B k) where

  gr_zero : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D), ∀ x ∈ (C.ring h).gr 0,
    ∃ c : ℚ, x = algebraMap ℚ _ c

  push : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X), π ≫ p = q → IsGenSmooth q π → ((C.ring h').CH →ₗ[ℚ] (C.ring h).CH)

  mem : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x ∈ (C.ring h).gr j

  eq_zero : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i : ℕ), i + D < D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x = 0

  proj : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (x : (C.ring h).CH) (y : (C.ring h').CH),
    push h h' π hπ hs (C.pull h h' π hπ x * y) = x * push h h' π hπ hs y

  om : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    h.IsFibreInt h' π hπ (h'.coeFld ((C.ring h').om y)) (h.coeFld ((C.ring h).om (push h h' π hπ hs y)))

  a : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ η, h'.IsArForm i η →
    ∃ η', h.IsArForm j η' ∧ h.IsFibreInt h' π hπ η η' ∧ push h h' π hπ hs ((C.ring h').a η) = (C.ring h).a η'

  deg : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    (C.ring h).deg (push h h' π hπ hs y) = (C.ring h').deg y

  push_id : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D),
    push h h (𝟙 X) (Category.id_comp p) (.of_smooth _) = LinearMap.id

  push_comp : ∀ {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} {D D' D'' : ℕ} (h : IsRegVar p D)
    (h' : IsRegVar q D') (h'' : IsRegVar t D'') (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (ρ : Z ⟶ Y)
    (hρ : ρ ≫ q = t) (hs' : IsGenSmooth t ρ) (hs'' : IsGenSmooth t (ρ ≫ π)),
    push h h'' (ρ ≫ π) (by rw [Category.assoc, hπ, hρ]) hs'' = push h h' π hπ hs ∘ₗ push h' h'' ρ hρ hs'

open Limits

def relCot (π : Y ⟶ X) : Y.Modules := Conormal.conormal (pullback.diagonal π)

def dRel (π : Y ⟶ X) (W : Y.Opens) (f : Γ(Y, W)) : Γ(relCot π, W) :=
  Conormal.d (pullback.diagonal_fst π) (V := W) (W := pullback.snd π π ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, pullback.diagonal_snd]; exact le_rfl) ((pullback.snd π π).app W f)

variable (q) in

def IsRelAcyclic (π : Y ⟶ X) (L : LB Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (W : κ → Y.Opens),
    (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = π ⁻¹ᵁ U → ∀ n, (AbLaw.cechLB q L W).ExactAt (n + 1)

end GlobalTheory.CxForm
