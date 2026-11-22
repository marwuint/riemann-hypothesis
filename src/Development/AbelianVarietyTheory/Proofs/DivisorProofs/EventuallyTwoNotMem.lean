import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure GoodPlace {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (χX : Chr F E) (v : Pl F) :
    Prop where

  inertOrSplit : (∃ w, Formalism.UG.IsInertAt F E v w) ∨ Nonempty (E →ₐ[F] Fv F v)

  two : (2 : 𝓞 F) ∉ v.asIdeal

  psi : PsiUnr B.ψ v

  vac : M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

  lat : ∀ l, l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ↔
    ∀ i, l.1 i ∈ v.adicCompletionIntegers F ∧ l.2 i ∈ v.adicCompletionIntegers F

  unr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w

end GlobalTheory.PairVac
