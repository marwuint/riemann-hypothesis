import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
import Formalism.GaussJetBounds.MonoShapeTop
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Slices

variable {R : Type u} [CommRing R] {T σ ρ : Type}

def bSlice (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) : σ →₀ ℕ :=
  κ.comapDomain (fun y => e (t, y)) (fun _ _ _ _ h => (Prod.mk.inj (he h)).2)

lemma bSlice_apply (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) (y : σ) :
    bSlice e he t κ y = κ (e (t, y)) := rfl

end Slices

end Formalism.DworkPowerSeriesWeights
