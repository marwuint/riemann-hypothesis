import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOPerm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower.TopGridExists

open Matrix in

theorem exists_isONBasis {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool}
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hs : s * B = B * Formalism.REAL.Jm ε) :
    ∃ (B' : Matrix (Fin k) (Fin k) ℂ) (p : ℕ), IsONBasis G s B' p := by
  obtain ⟨π, hπ⟩ := GlobalTheory.FockOrder.exists_sortPerm ε
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hπ
  have hJ : (Matrix.diagonal fun a => (((if ε a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases ε a <;> simp
  refine ⟨B.submatrix id π, p, fun a => if a.val < p then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : a.val < p
    · left; simp [ha]
    · right; simp [ha, not_lt.1 ha]
  · have e : (B.submatrix id π)ᴴ * G * B.submatrix id π = (Bᴴ * G * B).submatrix π π := by
      ext a b; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, hG, ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; simp [hπ a]
  · have e : s * B.submatrix id π = (s * B).submatrix id π := by
      ext a b; simp [Matrix.mul_apply]
    rw [e, hs, ← Matrix.submatrix_mul_equiv (e₂ := π), ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 2; funext a; simp [hπ a]

open Matrix GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in

theorem exists_rig_of_frame {D : D7} {V : HSp D} (A : Fr V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.s = A.cart ∧ r.Is := by
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hΛ.1
  have hτ : ∀ τ : D.what₂.Tau, ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ),
      IsONBasis (gramAt D V τ) (A.cart τ) B p := fun τ => by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    have h1 := Matrix.mul_nonsing_inv _ hu
    refine exists_isONBasis (B := (A.fr τ)⁻¹) (ε := A.ε τ) ?_ ?_
    · rw [← A.fr_gram τ]
      simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
    · simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
  choose B hB using hτ
  exact ⟨⟨Λ, β, A.cart, B⟩, rfl, rfl, hΛ, hβ, fun τ => ⟨GlobalTheory.CompactFockAction.cart_isCartanInv A τ, hB τ⟩⟩

end GlobalTheory.SqTower.TopGridExists

end
