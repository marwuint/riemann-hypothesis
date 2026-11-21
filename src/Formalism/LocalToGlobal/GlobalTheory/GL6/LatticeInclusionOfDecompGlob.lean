import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

theorem bwA_natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  first
    | exact lam.natW_anti
    | exact lam.anti
    | exact lam.antitone
    | (intro a b hab
       simp only [DomWeight.natW]
       first
         | (have := lam.anti hab; omega)
         | (have := lam.dom hab; omega)
         | (have := lam.antitone hab; omega)
         | (have := lam.mono hab; omega)
         | (have := lam.2 hab; omega)
         | (have := lam.dom a b hab; omega)
         | (have := lam.2 a b hab; omega)
         | (have := lam.w_anti hab; omega)
         | (have := lam.anti a b hab; omega))

theorem bwA_val_locInt (w : D.what₂.places.Pl) (σ : D.host.E →+* D.host.E) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E).range) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ y)) := by
  obtain ⟨a, ha⟩ := hy
  have hint : IsIntegral ℤ (D.embE (σ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E a))) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.embE.comp σ).toIntAlgHom)
  have h0 := bwA_val_integral_nonneg D.what₂.places w _ hint
  rw [ha, map_mul, map_mul, map_natCast, map_natCast, AddValuation.map_mul,
    bwA_val_nat_eq_zero D.what₂.places w s hs, zero_add] at h0
  exact h0

def bwA_EO (O : Subring ℂ) (N : ℕ) : Submonoid (Matrix (Fin N) (Fin N) ℂ) :=
  Submonoid.closure {g | ∃ (a b : Fin N) (c : ℂ), c ∈ O ∧ g = 1 + Matrix.single b a c}

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
