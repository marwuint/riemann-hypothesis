import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
import Formalism.HermitianLattices.FinalMass

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trace_inner_self_pos {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : IsPosDef h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have key : ((Algebra.trace ℚ K (h x x) : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ (h x x) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have key' : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re key
    rw [Complex.re_sum] at this
    rw [← this]
    simp
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    let σ0 : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) ⟨σ0, Finset.mem_univ _⟩
  exact_mod_cast key' ▸ hpos

section Rows

open Classical

def FibresOrthLatticeOneGenus (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    (∀ Λ' ∈ s, L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0))) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
      ∑ Λ' ∈ s.filter (fun Λ' => ∃ g ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, Formalism.HermitianLatticesTheory.gmap g M = L0X D Λ' (lf D F0)),
          wRow D F0 Λ' =
        ((Tu D u : ℝ) - 1) ^ D.R.f * ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) : ℕ) : ℝ)⁻¹

theorem sum_eq_sum_over_class_reps {K V α : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (reps : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L reps) (s : Finset α)
    (c : α → Submodule (𝓞 K) V) (hc : ∀ a ∈ s, c a ∈ Formalism.HermitianLatticesTheory.genus h L) (w : α → ℝ) :
    ∑ a ∈ s, w a = ∑ M ∈ reps, ∑ a ∈ s.filter (fun a => ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M = c a), w a := by
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro ha
      obtain ⟨N, ⟨hN, hg⟩, _⟩ := hreps.2 (c a) (hc a ha)
      exact ⟨N, hN, ha, hg⟩
    · rintro ⟨N, _, ha, _⟩
      exact ha
  · intro M hM M' hM' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_filter] at ha ha'
    obtain ⟨N, _, huniq⟩ := hreps.2 (c a) (hc a ha.1)
    exact hne ((huniq M ⟨hM, ha.2⟩).trans (huniq M' ⟨hM', ha'.2⟩).symm)

theorem gluing_mass_of_fibre_structure (D : D7) (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hR : FibresOrthLatticeOneGenus D u) : WordRowsGluing D u := by
  intro hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨hgen, hfib⟩ := hR hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨⟨reps, hreps⟩, hmass, _⟩ := Formalism.HermitianLatticesTheory.final_massBasic D.host.E (D.sp.X 0).V (D.sp.X 0).hT (D.sp.X 0).herm
    (trace_inner_self_pos _ hpos) (L0X D Λ (lf D F0)) (hlat hT h3 hsp F0 he hz Λ hΛ)
  rw [hmass reps hreps]
  unfold massRows
  rw [sum_eq_sum_over_class_reps (D.sp.X 0).hT _ reps hreps s (fun Λ' => L0X D Λ' (lf D F0)) hgen,
    Finset.sum_congr rfl fun M hM => hfib M (hreps.1 M hM), ← Finset.mul_sum, mul_comm]

end Rows

end Formalism.MainNotions.BridgeLemma₂

end
