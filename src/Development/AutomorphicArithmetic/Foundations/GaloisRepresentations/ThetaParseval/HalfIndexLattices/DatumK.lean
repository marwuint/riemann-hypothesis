import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem resEta_mul (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) : ResEtaF (η * κ) 1 :=
  ⟨h2.1, fun e he a => by rw [MonoidHom.mul_apply, hκ.base a, mul_one]; exact h2.2 e he a⟩

end UpperTheory.TP.W

end
