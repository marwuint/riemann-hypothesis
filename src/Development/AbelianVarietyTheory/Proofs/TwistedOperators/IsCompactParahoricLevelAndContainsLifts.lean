module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricCompact

theorem exists_compact_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x ∈ St β → ∀ i j, x.1 i j ∈ C := by
  classical
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨-, C0, hC0, hC0m⟩ := GlobalTheory.Mass.intTens_open_compact F E
  let s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)

  let b := (β : Matrix (Fin n) (Fin n) _).map s.symm
  let c := ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map s.symm

  let f : Fin n → Fin n →
      (Fin n → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) →
        _ :=
    fun i j a => ∑ l, (∑ k, b i k * a k l) * c l j
  have hf : ∀ i j, Continuous (f i j) := fun i j =>
    continuous_finsetSum _ fun l _ =>
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_apply l).comp (continuous_apply k))).mul continuous_const
  have hS : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC0
  refine ⟨⋃ i, ⋃ j, f i j '' Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hS.image (hf i j), ?_⟩
  intro x hx i j
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    ⟨fun k l => s.symm (y.1 k l), ?_, ?_⟩⟩⟩
  · intro k _ l _
    apply hC0m
    change s (s.symm _) ∈ Formalism.L2.Herm.intAf F E
    rw [RingEquiv.apply_symm_apply]
    exact (y.1 k l).2
  · have hx' : x.1 i j = s.symm ((Formalism.UG.bc (s : _ →+* _) x).1 i j) := by
      rw [Formalism.UG.P.bc_coe]
      simp
    have hy' : Formalism.UG.bc (s : _ →+* _) x = β * Formalism.L2.DIV.intGL F E n y * β⁻¹ := by
      rw [← hy]
      rfl

    rw [hx', hy', Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [map_mul, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Formalism.L2.DIV.intGL, Formalism.UG.P.bc_coe]
    rfl

variable {D : D7}

theorem isOpen_comap_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hκ
  obtain ⟨hU, hS, hR⟩ := hκ
  show finE V κ ∈ lev D.sp.cm V.gram β L
  refine Formalism.L2.DIV.Kg_le_lev (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ?_
  simp only [Formalism.L2.DIV.Kg, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨⟨hU, hS⟩, fun PP hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hR PP hPP⟩⟩

theorem exists_compact (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, k ∈ GfC V → finE V k ∈ St β → k ∈ C := by
  obtain ⟨C1, hC1, hC1m⟩ := exists_compact_entries (F := D.host.F) (E := D.host.E) β
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C1 hC1

  haveI : T2Space (InfiniteAdeleRing D.host.F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  haveI : T2Space (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    inferInstanceAs (T2Space (RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
      (fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))) Filter.cofinite))
  haveI : T2Space (AF D.host.F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  obtain ⟨K', hK', hK'm⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) K hK
  refine ⟨K', hK', fun k hk hst => hK'm k fun i j => hKm _ ?_ ?_⟩
  ·
    have hsw : (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _) = swapAE D :=
      RingHom.ext fun _ => rfl
    have hst' : Formalism.UG.bc (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _)
        (finHom V k) ∈ St β := by
      rw [hsw]
      exact hst
    have h := hC1m (finHom V k) hst' i j
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe] at h
    exact h
  ·
    intro ρ
    have h1 : infHom V k = 1 := hk
    have h2 : infPart D ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram k : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
      have h3 := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j) h1
      simp only [infHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Units.val_one] at h3
      exact h3
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, norm_one, le_refl]
    · simp only [Matrix.one_apply_ne hij, map_zero, norm_zero, zero_le_one]

theorem isCompact_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsCompact ((levG V β L : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  obtain ⟨C, hC, hCm⟩ := exists_compact V β
  refine hC.of_isClosed_subset ?_ ?_
  · rw [levG, levA, Subgroup.coe_inf]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter
      (Subgroup.isClosed_of_isOpen _ (isOpen_comap_lev V β L))
  · intro k hk
    rw [SetLike.mem_coe, levG, levA, Subgroup.mem_inf] at hk
    exact hCm k hk.1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2))

theorem isCompact_flag_and_lift : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  intro D V β L
  refine ⟨isCompact_levG V β (flagL L), fun g0 κ hκ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hκ
  rw [levG, levA, Subgroup.mem_inf]
  refine ⟨h1, ?_⟩
  show finE V κ ∈ lev D.sp.cm V.gram β (flagL L)
  rw [Formalism.L2.DIV.mem_lev]
  exact ⟨h2, Subgroup.mem_top _⟩

end GlobalTheory.ParahoricCompact
