import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.CmDim

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 4 * D.R.ord := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.toFrame.natCard_GG
  rw [← h2, ← h1, h4]

theorem two_mul_card_psi (φ : Formalism.HC.Frame) : 2 * Nat.card φ.Psi = 4 * φ.ord := by
  classical
  have h4 : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have hfin : Finite φ.GG := Nat.finite_of_card_ne_zero (by rw [h4]; have := φ.ord_pos; omega)
  have e1 : {g : φ.GG // g ∈ φ.Psi} ≃ {g : φ.GG // ¬ g ∈ φ.Psi} :=
    (Equiv.mulRight φ.cc).subtypeEquiv fun g => mem_Psi_iff_mul_cc_notMem g
  have h1 := Nat.card_congr (Equiv.sumCompl fun g : φ.GG => g ∈ φ.Psi)
  rw [Nat.card_sum, ← Nat.card_congr e1, h4] at h1
  exact (two_mul _).trans h1

theorem card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.E / 2 := by
  have h1 := two_mul_card_psi D.R.toFrame
  have h2 := Nat.card_congr D.eTau
  rw [Nat.card_eq_fintype_card] at h2
  have h3 := finrank_host D
  omega

end GlobalTheory.ShFam.CmDim
