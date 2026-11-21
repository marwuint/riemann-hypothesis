import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {X Y Y' : Scheme.{0}}

abbrev Inn {B : Type} [CommRing B] (y : Sp B ⟶ Y) (U : Y.Opens) : Prop := ⊤ ≤ y ⁻¹ᵁ U

section
variable {B B' : Type} [CommRing B] [CommRing B'] {y : Sp B ⟶ Y} {U V : Y.Opens}

theorem Inn.mono (h : Inn y U) (e : U ≤ V) : Inn y V := fun _ hp ↦ e (h hp)

theorem Inn.inf (h : Inn y U) (h' : Inn y V) : Inn y (U ⊓ V) := fun _ hp ↦ ⟨h hp, h' hp⟩

theorem valR_resU (e : V ≤ U) (h : Inn y V) (f : Γ(Y, U)ˣ) : valR y V (res e f).val = valR y U f.val :=
  valR_res y e h f.val

theorem valR_inv_mul (h : Inn y U) (f : Γ(Y, U)ˣ) : valR y U (f⁻¹).val * valR y U f.val = 1 := by
  rw [← valR_mul _ _ h, Units.inv_mul, valR_one _ _ h]

end

abbrev Kap (Y : Scheme.{0}) : Type 1 :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (_ : B →+* B') (_ : Sp B ⟶ Y), B'

def Rel (N : LB Y) (κ : Kap Y) : Prop :=
  ∃ w : N.ι → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ,
    (∀ (i j : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → Inn y (N.U j) →
      (w i B y).val = valR y (N.U i ⊓ N.U j) (N.g i j).val * (w j B y).val) ∧
    ∀ (i : N.ι) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (N.U i) →
      (w i B' (spMap ρ ≫ y)).val = ρ (w i B y).val * κ B B' ρ y

variable {N N' : LB Y} {κ κ' κ'' : Kap Y}

theorem Rel.twist (h : Rel N κ) (u : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ' B B' ρ y * ρ (u B y).val = κ B B' ρ y * (u B' (spMap ρ ≫ y)).val) : Rel N κ' := by
  obtain ⟨w, h1, h2⟩ := h
  refine ⟨fun i B _ y ↦ w i B y * u B y, fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · simp only [Units.val_mul]
    rw [h1 i j B y hi hj, mul_assoc]
  · simp only [Units.val_mul, map_mul]
    rw [h2 i B B' ρ y hi]
    linear_combination -ρ (w i B y).val * e B B' ρ y

theorem Rel.congr (h : Rel N κ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), κ' B B' ρ y = κ B B' ρ y) :
    Rel N κ' :=
  h.twist (fun _ _ _ ↦ 1) fun B B' _ _ ρ y ↦ by rw [e, Units.val_one, Units.val_one, map_one]

theorem Rel.div (h : Rel N κ) (h' : Rel N' κ')
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ'' B B' ρ y * κ' B B' ρ y = κ B B' ρ y) : Rel (LB.div N N') κ'' := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨w', h1', h2'⟩ := h'
  refine ⟨fun p B _ y ↦ w p.1 B y * (w' p.2 B y)⁻¹, fun p q B _ y hp hq ↦ ?_, fun p B B' _ _ ρ y hp ↦ ?_⟩
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have hq' : Inn y (N.U q.1 ⊓ N'.U q.2) := hq
    have hy : Inn y (N.U p.1 ⊓ N'.U p.2 ⊓ (N.U q.1 ⊓ N'.U q.2)) := hp'.inf hq'
    have a1 := h1 p.1 q.1 B y (hp'.mono inf_le_left) (hq'.mono inf_le_left)
    have a2 := h1' p.2 q.2 B y (hp'.mono inf_le_right) (hq'.mono inf_le_right)
    have a3 := valR_inv_mul ((hp'.mono inf_le_right).inf (hq'.mono inf_le_right)) (N'.g p.2 q.2)
    have a4 : ((w' p.2 B y)⁻¹).val * (w' p.2 B y).val = 1 := Units.inv_mul _
    have a5 : ((w' q.2 B y)⁻¹).val * (w' q.2 B y).val = 1 := Units.inv_mul _
    have a6 : valR y ((LB.div N N').U p ⊓ (LB.div N N').U q) ((LB.div N N').g p q).val =
        valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val * valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val := by
      refine (valR_mul y _ hy _ _).trans (congrArg₂ (· * ·) (valR_resU _ hy _) ?_)
      exact valR_resU (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hy
        (N'.g p.2 q.2)⁻¹
    rw [a6]
    simp only [Units.val_mul]
    rw [a2] at a4
    rw [a1]
    generalize valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val = G at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val = Gi at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) (N'.g p.2 q.2).val = G' at *
    generalize ((w' p.2 B y)⁻¹).val = a at *
    generalize ((w' q.2 B y)⁻¹).val = b at *
    generalize (w' q.2 B y).val = c at *
    generalize (w q.1 B y).val = d at *
    have k : a = Gi * b := by linear_combination (-a * b * c) * a3 - a * a5 + Gi * b * a4
    rw [k]; ring
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have a1 := h2 p.1 B B' ρ y (hp'.mono inf_le_left)
    have a2 := h2' p.2 B B' ρ y (hp'.mono inf_le_right)
    have a4 : ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val * (w' p.2 B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have a5 : ρ ((w' p.2 B y)⁻¹).val * ρ (w' p.2 B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [Units.val_mul, map_mul]
    rw [a2] at a4
    rw [a1, ← e]
    generalize ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val = a' at *
    generalize ρ ((w' p.2 B y)⁻¹).val = a at *
    generalize ρ (w' p.2 B y).val = c at *
    have k : a' * κ' B B' ρ y = a := by linear_combination a * a4 - a' * κ' B B' ρ y * a5
    rw [← k]; ring

theorem Rel.pull (h : Rel N κ) (ψ : Y' ⟶ Y) : Rel (N.pull ψ) fun B B' _ _ ρ y ↦ κ B B' ρ (y ≫ ψ) := by
  obtain ⟨w, h1, h2⟩ := h
  have hin : ∀ (j : PUnit → N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y'), Inn y ((N.pull ψ).U j) →
      Inn (y ≫ ψ) (N.U (j PUnit.unit)) := fun j B _ y h p _ ↦
    LB.wchart_le N (K := PUnit) (fun _ ↦ ψ) j PUnit.unit (h (Set.mem_univ p))
  refine ⟨fun j B _ y ↦ w (j PUnit.unit) B (y ≫ ψ), fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · refine (h1 _ _ B _ (hin i B y hi) (hin j B y hj)).trans (congrArg (· * _) ?_)
    have a := (hin i B y hi).inf (hin j B y hj)
    have b := hi.inf hj
    exact (valR_eq _ _ a _).trans ((GlobalTheory.DeRham.evalAt_pull_g N ψ y i j a b).trans (valR_eq y _ b _).symm)
  · have := h2 _ B B' ρ _ (hin i B y hi)
    rw [← Category.assoc] at this
    exact this

end CrystallinePoints.Pd
