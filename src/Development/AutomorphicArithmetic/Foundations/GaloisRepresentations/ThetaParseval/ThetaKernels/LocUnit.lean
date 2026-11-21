import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocUnit

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem UpperTheory.TP.K.exists_locUnit {B : Base F E} (hB : UpperTheory.TP.W.GoodK σ B) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl F) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      sigR (Fv F v) σ (u : Fv F v ⊗[F] E) = -(u : Fv F v ⊗[F] E) :=
  _root_.UpperTheory.Reformulated.B.Gs6.exists_locUnit hB hξ hσξ v

end
