import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedUnipotentRadicalAtRealPlaceTrivialAtPlac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalAtRealPlaceCommuteInfTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalEqAtRealPlaceMulTrivialAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelIndicatorTestFunctionFactorAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealComponentFrameHomUnitaryDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingRealComponentUnipotentRadical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

open GlobalTheory.FibreAtTau

variable {D : D7}

theorem isHaarSub_map_closedEmb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : GlobalTheory.Dec.IsHaarSub (N : Set H) ν) :
    GlobalTheory.Dec.IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hm : Measurable ι := hι.continuous.measurable
  have hc : IsClosed ((N.map ι : Subgroup G) : Set G) := hι.isClosedMap _ hN
  obtain ⟨h0, hK, hc0, hinv⟩ := hν
  refine ⟨?_, ⟨fun K hK' => ?_⟩, ?_, ?_⟩
  · rwa [Ne, Measure.map_eq_zero_iff hm.aemeasurable]
  · rw [Measure.map_apply hm hK'.isClosed.measurableSet]
    exact (hι.isCompact_preimage hK').measure_lt_top
  · rw [Measure.map_apply hm hc.measurableSet.compl]
    refine measure_mono_null (fun z hz hzN => hz ⟨z, hzN, rfl⟩) hc0
  · rintro _ ⟨m, hmN, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hm]
    have : ((fun x => ι m * x) ∘ ι) = ι ∘ (fun x => m * x) := by
      funext x; simp
    rw [this, ← Measure.map_map hm (measurable_const_mul _), hinv m hmN]

theorem isHaarSub_top {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] : GlobalTheory.Dec.IsHaarSub ((⊤ : Subgroup H) : Set H) ν := by
  refine ⟨NeZero.ne ν, inferInstance, by simp, fun m _ => MeasureTheory.map_mul_left_eq_self ν m⟩

theorem L_closed (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    IsClosed (atP θ V C τ : Set (NI V C)) ∧ IsClosed (offP θ V C τ : Set (NI V C)) :=
  _root_.GlobalTheory.FibreAtTau.isClosed_atP_and_isClosed_offP D θ hθ V r C τ

theorem L_comm (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    (∀ p ∈ atP θ V C τ, ∀ q ∈ offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ atP θ V C τ → h ∈ offP θ V C τ → h = 1 :=
  _root_.GlobalTheory.FibreAtTau.comm_and_inf_trivial D θ hθ V r C τ

theorem L_decomp (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : IsIsoFrame V C) (τ : D.what₂.Tau) (h : NI V C) : ∃ p ∈ atP θ V C τ, ∃ q ∈ offP θ V C τ, h = p * q :=
  GlobalTheory.T.unipotentRadical_eq_atRealPlace_mul_trivialAtPlace D θ hθ V r C hC τ h

theorem L_factor (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C) (hq : q ∈ offP θ V C τ) (x y : GA D V) :
    ∃ R : ℂ, ∀ p ∈ atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R :=
  _root_.GlobalTheory.FibreAtTau.coef_factor D θ hθ V S M K v a τ r C q hq x y

theorem L_hom (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ),
      ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
  _root_.GlobalTheory.FibreAtTau.cmp_frame_hom D θ hθ V S M τ

theorem L_emb (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (E : GA D V →* Formalism.REAL.UJ (M.ε τ)) (hE : ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) :
    ∃ W : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.Dec.IsIsoC (M.ε τ) W ∧
      Topology.IsClosedEmbedding (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) ∧
      Set.range (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) = GlobalTheory.Dec.NW (M.ε τ) W :=
  _root_.GlobalTheory.FibreAtTauEmb.isClosedEmbedding_atP D θ hθ V S M τ r C hC E hE

end GlobalTheory.FibreAtTau
