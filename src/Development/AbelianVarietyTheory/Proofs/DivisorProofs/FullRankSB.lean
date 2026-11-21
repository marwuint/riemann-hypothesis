import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev blocks (a b : ℕ) : (Σ x, Two (Fin a) (Fin b) x) ≃ Fin (a + b) := two (stdSum (rfl : a + b = a + b))

def parChar (ν β : kˣ →* ℂˣ) (a b : ℕ) : parab k (blocks a b) →* ℂˣ :=
  (deltaHalf k (Two (Fin a) (Fin b)) * ((detChar (Fin a) (ν * β)).comp (MonoidHom.fst _ _)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom *
    ((detChar (Fin b) β).comp (MonoidHom.snd _ _)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom).comp
    (leviProj k (blocks a b))

def indScal (ν β : kˣ →* ℂˣ) (a b : ℕ) : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
  smoothPart (rightReg ℂ (GL (Fin (a + b)) k) ℂ) ⊓ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b))

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.RankFibre
