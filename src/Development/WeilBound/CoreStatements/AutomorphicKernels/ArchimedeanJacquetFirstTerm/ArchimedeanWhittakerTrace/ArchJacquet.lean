import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.FTA.FunctionalEquationHypotheses.B2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

structure Hyp (B : Base F E) (Y : Spc F E n) (χ : Chr F E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) : Prop where
  good : B.IsGood σ
  hn : 1 ≤ n
  sign : ∃ r s, Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s
  hecke : IsHecke F E χ
  res : ∃ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c
  stab : IsStab2 B K
  hgt : IsHgt K a

end PositivityTheory.FTA.FunctionalEquationHypotheses.B2

end
