import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.TateCompare

variable {p : ℕ} [Fact p.Prime] {D : Datum p}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_zsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℤ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  let φ : Multiplicative D.La →* Q := MonoidHom.mk' (fun y => I.ev n y.toAdd) (fun a b => I.add n _ _)
  exact map_zpow φ (Multiplicative.ofAdd x) c

theorem ev_eq_iff (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) {x y : D.La} :
    I.ev n x = I.ev n y ↔ ∃ z, x = y + n • z := by
  constructor
  · intro h
    have h₁ : I.ev n y * I.ev n (x - y) = I.ev n y * 1 := by
      rw [← I.add, add_sub_cancel, h, _root_.mul_one]
    obtain ⟨z, hz⟩ := (I.ker n hn hc _).1 (mul_left_cancel h₁)
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  · rintro ⟨z, rfl⟩
    exact I.ev_add_nsmul hn hc _ _

theorem exists_lift (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ g : D.La →+ D.La, 0 < n → n.Coprime p → ∀ y, I₁.ev n (g y) = I₂.ev n y := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hpre : ∀ y, ∃ x, I₁.ev n x = I₂.ev n y := fun y =>
    (I₁.onto n hn hc _).1 ((I₂.onto n hn hc _).2 ⟨y, rfl⟩)
  choose f hf using hpre
  let g : D.La →ₗ[ℤ] D.La := b.constr ℤ (fun i => f (b i))
  refine ⟨g.toAddMonoidHom, fun _ _ y => ?_⟩
  show I₁.ev n (g y) = I₂.ev n y
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [g, Module.Basis.constr_basis, hf]
  | zero =>
    rw [map_zero, (I₁.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩, (I₂.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩]
  | add x y _ _ hx hy => rw [map_add, I₁.add, I₂.add, hx, hy]
  | smul c x _ hx => rw [map_zsmul, ev_zsmul, ev_zsmul, hx]

theorem exists_mult (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ u : ℕ, 0 < n → n.Coprime p → I₁.ζ n ^ u = I₂.ζ n := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ : IsPrimitiveRoot ((I₁.ζ n : kˣ) : k) n := IsPrimitiveRoot.coe_units_iff.2 (I₁.ζ_prim n hn hc)
  have h₂ : ((I₂.ζ n : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (I₂.ζ_prim n hn hc).pow_eq_one, Units.val_one]
  obtain ⟨u, -, hu⟩ := h₁.eq_pow_of_pow_eq_one h₂
  exact ⟨u, fun _ _ => Units.ext (by rw [Units.val_pow_eq_pow_val, hu])⟩

end GlobalTheory.UPel.HT.TateCompare
