import Formalism.GaussJetBounds.StatementP

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

def serAlong {K : Type} [Field K] {ι κ : Type} (e : ι → κ) (f : MvPowerSeries ι K) :
    MvPowerSeries κ K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X (e i) : MvPowerSeries κ K)) f

def opAlong {K : Type} [Field K] {ι κ σ τ : Type} (e : ι → κ) (e' : σ → τ)
    (P : MvPolynomial ι (MvPolynomial σ K)) : MvPolynomial κ (MvPolynomial τ K) :=
  MvPolynomial.rename e (MvPolynomial.map (MvPolynomial.rename e' : MvPolynomial σ K →ₐ[K]
    MvPolynomial τ K).toRingHom P)

end Formalism.DworkPowerSeriesWeights
