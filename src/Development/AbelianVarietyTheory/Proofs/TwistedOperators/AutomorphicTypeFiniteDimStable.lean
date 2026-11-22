import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum
end GlobalTheory.FiniteGKSum
