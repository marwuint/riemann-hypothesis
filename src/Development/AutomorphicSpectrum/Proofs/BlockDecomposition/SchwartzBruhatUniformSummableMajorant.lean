import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.GodementEis
import GroundTheory.GlobalFields.TateThesis.TateMain

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

end

end GlobalTheory.CompanionTheory.EisRk1Bound
