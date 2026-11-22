import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

def cns_Ok (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∃ h : ℝ, GapAtLeast ε lam h ∧ thrStar ε < h) ∧ StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
    (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))

theorem cns_data' {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), cns_Ok ε lam T Ψ := by
  obtain ⟨T, Ψ, h1, h2, h3, h4, h5, h6⟩ := cns_data hq hlam hh hth
  exact ⟨T, Ψ, ⟨h, hh, hth⟩, h1, h2, h3, h4, h5, h6⟩

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

end ReciprocityTheory.ChartRestriction.DS
