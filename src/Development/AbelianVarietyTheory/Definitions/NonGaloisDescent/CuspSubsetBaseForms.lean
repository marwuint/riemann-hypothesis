import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead.Test

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

def idCov (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (nab : NabV (T.Q.Xo j) T.Q.c) : Cover T j σ where
  c' := T.Q.c
  hle := le_rfl
  d := GlobalTheory.RawSpan.idCover nab 0
  σ₂ := σ
  U₂ := T.U j σ
  dict₂ := T.dict j σ
  cc₂ := T.cE j σ

theorem idCov_rd (nab : NabV (T.Q.Xo j) T.Q.c) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    (idCov T j σ nab).rd a f = T.phiJ j σ a f := rfl

theorem idCov_ratForms (nab : NabV (T.Q.Xo j) T.Q.c) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (idCov T j σ nab).ratForms a n = baseForms T j σ a n := rfl

theorem rd_apply (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) (g : GA D (T.V j σ)) :
    C.rd a f₂ g = C.cc₂ (C.dict₂ g).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g *
      rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) := by
  simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
  ring

abbrev withC (C : Cover T j σ) (cc : C.U₂.Comp → ℂ) : Cover T j σ := { C with cc₂ := cc }

theorem isUnif_withC (C : Cover T j σ) (cc : C.U₂.Comp → ℂ) : (withC C cc).IsUnif ↔ C.IsUnif := Iff.rfl

theorem zero_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : 0 ∈ C.ratForms a n := by
  refine ⟨0, ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩, ?_⟩
  funext g
  rw [rd_apply, map_zero]
  simp

theorem add_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {φ ψ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ C.ratForms a n) (hψ : ψ ∈ C.ratForms a n) : φ + ψ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  obtain ⟨f', hf', rfl⟩ := hψ
  refine ⟨f + f', ⟨Submodule.add_mem _ hf.1 hf'.1, by rw [map_add]; exact Submodule.add_mem _ hf.2 hf'.2⟩, ?_⟩
  funext g
  simp only [Pi.add_apply, rd_apply, map_add]
  ring

theorem smul_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ C.ratForms a n) : C.σ₂ x • φ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  refine ⟨x • f, ⟨Submodule.smul_mem _ _ hf.1, by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩, ?_⟩
  funext g
  simp only [Pi.smul_apply, rd_apply, map_smulₛₗ, smul_eq_mul]
  ring

end GlobalTheory.CoverRead.Test
