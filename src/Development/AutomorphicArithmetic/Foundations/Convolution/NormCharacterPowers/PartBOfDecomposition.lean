import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

end Pb2

open Pb2

end UpperTheory.ConvolutionTheory.R
