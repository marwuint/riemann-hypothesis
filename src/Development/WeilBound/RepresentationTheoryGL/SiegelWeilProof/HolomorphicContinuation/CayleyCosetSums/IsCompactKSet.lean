import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConvPhi
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

end PositivityTheory.Rg.Sw.HSt.Conv
