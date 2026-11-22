import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFJCutFF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ n : ℕ, B.JF p.T.base (fun g => cutN P.k P.r n g • f g) ∈ FFKB p

end

end Formalism.FourierDecayAlt.P.CutBP
