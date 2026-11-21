import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TilX Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopPtModel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_mul {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (a b : GL (Fin N) (AfE F E)) :
    ((a * b : GL (Fin N) (AfE F E)).1).map (adAt F P) = a.1.map (adAt F P) * b.1.map (adAt F P) := by
  rw [Units.val_mul, Matrix.map_mul]

theorem adAt_of_prV {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {k : GL (Fin N) (AfE F E)}
    (h1 : bc (prV (E := E) (P.under (𝓞 F))) k = 1) : k.1.map (adAt F P) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h2 : prV (E := E) (P.under (𝓞 F)) (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin N) _ => g.1 i j) h1
    simp only [Units.val_one] at h3
    have h4 : prV (E := E) (P.under (𝓞 F)) (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem topPt_base {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k) :
    PtOf k (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)) := by
  have := h (DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rwa [one_mul] at this

end GlobalTheory.Mem.Col2.TopPtModel

end
