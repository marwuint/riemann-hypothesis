import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_du_nat (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (C : FC) (cD ch : ℝ) (P : PreCh) (q1 : ℕ)
    (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
    ∃ du : P.Word → ℕ, (∀ u, 0 < du u) ∧ ∀ u, (du u : ℝ) = duP P u := by
  obtain ⟨x0, h⟩ := Inh.g_big eps h0 h1
  refine ⟨x0, fun s C cD ch P q1 a b c hs hx hok => ?_⟩
  choose du hpos hdu using fun u => DuInt.duStarOf_nat P.R P.H (P.hcW u) hok.arith.2.1
    fun i => h s P.R _ hs hx hok.rank (hok.val.2.2.2.2.1 i).1
  exact ⟨du, hpos, hdu⟩

namespace Inh

end Inh

end GlobalTheory.Mem.Top

end
