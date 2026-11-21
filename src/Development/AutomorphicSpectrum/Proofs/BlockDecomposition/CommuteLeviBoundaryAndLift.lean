import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
