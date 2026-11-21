import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

private def UpperTheory.GL.jac (l : ℕ) : ℕ →* ℤ where
  toFun a := jacobiSym (a : ℤ) l
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, jacobiSym.mul_left]

