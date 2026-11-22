import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerLeviDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieAlgebraExpGenerators

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Smooth

theorem pi_exp {ι 𝔸 : Type} [Fintype ι] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (Y : ι → 𝔸) (i : ι) :
    NormedSpace.exp Y i = NormedSpace.exp (Y i) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ _
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact Pi.coe_exp Y i

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (e : ℕ) (γ : Fin e → ℝ → GAd σ J)
      (Z : Fin e → InfinitePlace F → Matrix (Fin n) (Fin n) ℂ), (∀ j t, γ j t ∈ infPts σ J) →
      (∀ (j : Fin e) (t : ℝ) (w : InfinitePlace F), GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w (γ j t)) = NormedSpace.exp (t • Z j w)) →
      (∀ Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * J.map (τ w).1 + J.map (τ w).1 * Y w = 0) →
        Y ∈ Submodule.span ℝ (Set.range Z)) →
      ∀ (m : ℕ) (u : (Fin m → ℝ) → GAd σ J), GlobalTheory.Orb.IsSmoothRealFam u → ∀ t₀ : Fin m → ℝ, u t₀ = 1 →
      ∃ s : (Fin m → ℝ) → Fin e → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s t₀ ∧
        ∀ᶠ t in 𝓝 t₀, u t = (List.ofFn fun j => γ j (s t j)).prod := by
  intro F E _ _ _ _ _ σ h n J _ τ e γ Z hγ hZ hspan m u hu t₀ h0
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let ι : GAd σ J →* (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :=
    MonoidHom.pi fun w => (GlobalTheory.Orb.archMat σ J (τ w)).comp (projArch σ J w)
  have hι : ∀ g w, ι g w = GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w g) := fun _ _ => rfl
  let S : Set (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) := {X | ∀ w, (X w)ᴴ * J.map (τ w).1 * X w = J.map (τ w).1}
  have hS : ∀ g, ι g ∈ S := fun g w => (archEquiv J h (τ w) (projArch σ J w g)).2
  have hpe : ∀ (Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) w, NormedSpace.exp Y w = NormedSpace.exp (Y w) :=
    fun Y w => pi_exp Y w
  have hZ' : ∀ j (t : ℝ), NormedSpace.exp (t • Z j) = ι (γ j t) := fun j t => funext fun w => by
    rw [hpe, hι, hZ]; rfl
  obtain ⟨s, hs, hev⟩ := _root_.GlobalTheory.ClosedMonoid.coords_second_kind_of_spanning (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) S
    (by
      simp only [S, Set.setOf_forall]
      exact isClosed_iInter fun w => isClosed_eq (((continuous_apply w).matrix_conjTranspose.matrix_mul
        continuous_const).matrix_mul (continuous_apply w)) continuous_const)
    (fun w => by simp)
    (fun a ha b hb w => by
      rw [Pi.mul_apply, Matrix.conjTranspose_mul]
      calc _ = (b w)ᴴ * ((a w)ᴴ * J.map (τ w).1 * a w) * b w := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [ha w, hb w])
    (fun Y hY w => by
      have h1 : (NormedSpace.exp (Y w))ᴴ * J.map (τ w).1 * NormedSpace.exp (Y w) = J.map (τ w).1 := hpe Y w ▸ hY w
      suffices (NormedSpace.exp ((-Y) w))ᴴ * J.map (τ w).1 * NormedSpace.exp ((-Y) w) = J.map (τ w).1 from
        (hpe (-Y) w).symm ▸ this
      have h2 : NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w) = 1 := by
        rw [Pi.neg_apply, ← Matrix.exp_add_of_commute _ _ (Commute.refl (Y w)).neg_right, add_neg_cancel,
          NormedSpace.exp_zero]
      calc _ = (NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w))ᴴ * J.map (τ w).1 *
            (NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w)) := by
            conv_lhs => rw [← h1]
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
    e Z (fun j t => hZ' j t ▸ hS _)
    (fun Y hY => hspan Y fun w => GlobalTheory.ClosedMatGroup.skew_of_exp_smul_mem _ _ fun t => by
      have h1 : (NormedSpace.exp ((t • Y) w))ᴴ * J.map (τ w).1 * NormedSpace.exp ((t • Y) w) = J.map (τ w).1 :=
        hpe (t • Y) w ▸ hY t w
      exact h1)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ι (u t) := contDiff_pi.2 fun w => by
    let T : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
    exact T.contDiff.comp (f := fun t i j => GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w (u t)) i j)
      (contDiff_pi.2 fun i => contDiff_pi.2 fun j => hu.2 w (τ w) i j)
  have h1 : ι (u t₀) = 1 := by rw [h0, map_one]
  refine ⟨fun t => s (ι (u t)), (h1 ▸ hs).comp t₀ hc.contDiffAt, ?_⟩
  have ht : Tendsto (fun t => ι (u t)) (𝓝 t₀) (𝓝 1) := h1 ▸ hc.continuous.tendsto t₀
  filter_upwards [ht.eventually hev] with t ht
  have h2 : ι (u t) = ι (List.ofFn fun j => γ j (s (ι (u t)) j)).prod := by
    rw [map_list_prod, List.map_ofFn]
    exact (ht (hS _)).trans (congrArg (fun f => (List.ofFn f).prod) (funext fun j => hZ' j _))
  refine ext_inf_fin σ J (GInf_ext σ J fun w => ?_) ?_
  · rw [projInfArch_projInf, projInfArch_projInf]
    exact (GlobalTheory.Orb.isEmbedding_archMat J h (τ w)).injective (congrFun h2 w)
  · rw [hu.1, eq_comm, ← mem_infPts]
    refine list_prod_mem fun z hz => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hγ j _

end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.SiegelSet (IsRealLine)
open GlobalTheory.Orb (archMat IsSmoothRealFam)

namespace GlobalTheory.ThK.CuspTransfer.Smooth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem line_fam (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : IsSmoothRealFam γ ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  choose y e1 e2 using hγ
  obtain rfl : γ = fun t => embArch σ J w (y t) := funext e1
  exact GlobalTheory.Orb.isSmoothRealFam_embArch h τ fun i j => by
    simp only [e2]; exact GlobalTheory.Orb.contDiff_exp_smul_entry Z i j

def Gen {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 ∧ ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ archMat σ J τ y = NormedSpace.exp (t • Z)

omit [NumberField E] in
theorem Gen.line {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}
    (h : Gen τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, h.1, h.2⟩

end GlobalTheory.ThK.CuspTransfer.Smooth

end
