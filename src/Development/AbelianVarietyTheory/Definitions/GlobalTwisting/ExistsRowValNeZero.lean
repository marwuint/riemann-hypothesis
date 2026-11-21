import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.KerRat

namespace GlobalTheory.PerQ.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

def mtE (h : I.Ok) (u : B.Word) (a : I.ι) :
    MtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL ≃ₗ[ℂ] (I.per l u a).Mt :=
  mtEquiv (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.Ps u (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ _ => 0) B.embLL (tilOk I h u a).2.2

theorem mtE_toMtP (h : I.Ok) (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    mtE I l h u a (toMtP (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL z) = rowForm I l h u a z := rfl

end GlobalTheory.PerQ.Model

end
