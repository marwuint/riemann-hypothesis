import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult

theorem strictAnti_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) : StrictAnti lam := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by obtain ⟨k, hk⟩ := hr; omega⟩
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

end GlobalTheory.TrMult

end
