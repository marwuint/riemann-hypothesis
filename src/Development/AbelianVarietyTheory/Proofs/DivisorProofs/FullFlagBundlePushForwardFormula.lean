import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := _root_.GlobalTheory.FlagPush.interPoly_swap_adjacent F X Y ι m E E' φ f hf gr hg
  refine _root_.GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  rw [hR, antisymm_chernRoots_mul_fibrePoint]

end GlobalTheory.FlagPushProof
