import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

def lamE (σ : D.host.E →+* ℂ) : D.host.E →+* ℂ_[p] := lam.comp (σ.codRestrict Qbar (emb_mem D σ))

def homP : D.host.K →+* ℂ_[p] := (lamE D lam D.host.φ₀).comp (algebraMap D.host.K D.host.E)

def homPbar : D.host.K →+* ℂ_[p] := (homP D lam).comp (conjK D)

theorem homP_conjK (c : D.host.K) : homP D lam (conjK D c) = homPbar D lam c := rfl

def conjO (a : 𝓞 D.host.K) : 𝓞 D.host.K :=
  ⟨conjK D (a : D.host.K), (RingOfIntegers.isIntegral_coe a).map (conjK D).toIntAlgHom⟩

theorem coe_conjO (a : 𝓞 D.host.K) : ((conjO D a : 𝓞 D.host.K) : D.host.K) = conjK D (a : D.host.K) := rfl

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

theorem vecOf_add (A A' : Matrix (Fin N') (Fin N) D.host.E) :
    vecOf D cc δ (A + A') = vecOf D cc δ A + vecOf D cc δ A' := by
  funext τ i j
  simp [vecOf, embV, tor0, mul_add]

end GlobalTheory.PlaceComponents
