import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsArchimedeanIdentity

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.KStableSums

def pureL {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' a f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {Ψ : (Fin n × Fin d → AF F) → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb) ∧ (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  choose f φ hf hSB hev he using fun i => (g i).2
  refine ⟨m, fun i => a i • f i, φ, fun i => (M.Pol ψ emb).smul_mem _ (hf i), fun i => ⟨hSB i, hev i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i]
  exact ((pureL (φ i)).map_smul (a i) (f i)).symm

def piEnd {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) : Module.End ℂ (Fin m → V) :=
  LinearMap.pi fun i => L ∘ₗ LinearMap.proj i

theorem piEnd_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (y : Fin m → V)
    (i : Fin m) : piEnd m L y i = L (y i) := rfl

theorem piEnd_pow_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (k : ℕ)
    (y : Fin m → V) (i : Fin m) : (piEnd m L ^ k) y i = (L ^ k) (y i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, piEnd_apply, ih, pow_succ', Module.End.mul_apply]

theorem isExp_piEnd {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (m : ℕ) :
    IsExp (piEnd m L) (piEnd m U) := by
  intro y l
  have hl : ∀ z : Fin m → V, l z = ∑ i, (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) (z i) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    simp [map_sum]
  have key : (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * l ((piEnd m L ^ k) y)) =
      fun k => ∑ i, ((k.factorial : ℂ))⁻¹ * (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) ((L ^ k) (y i)) := by
    funext k
    rw [hl, Finset.mul_sum]
    simp only [piEnd_pow_apply]
  rw [key, hl]
  exact hasSum_sum fun i _ => h (y i) _

theorem exp_conj_rect {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (C : Matrix β ι ℂ) (A' : Matrix ι β ℂ) (hCA : C * A' = 1) (hAC : A' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * A') = C * NormedSpace.exp Y * A' := by
  let f : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * A'
      map_one' := by simp [hCA]
      map_mul' := fun X Z => by
        calc C * (X * Z) * A' = C * X * (A' * C) * Z * A' := by rw [hAC, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun X Z => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem atPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) : atPl (V := V) w 0 = 0 := by
  unfold atPl
  exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type}
    [Fintype κ] (act : Matrix κ κ ℂ →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) (w : ι) (Y : Matrix κ κ ℂ) :
    sumPl (V := fun _ : ι => V) (fun w' => act ((Pi.single w Y : ι → Matrix κ κ ℂ) w') +
        (c w' * ((Pi.single w Y : ι → Matrix κ κ ℂ) w').trace) • 1) =
      atPl (V := fun _ : ι => V) w (act Y + (c w * Y.trace) • 1) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp only [Pi.single_eq_of_ne hw', map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
    exact atPl_zero w'
  · intro h; exact absurd (Finset.mem_univ w) h

theorem exists_line_upq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {β : Type} [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (J : Matrix β β (AE F E)) (b : ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ)
    (hCM : IsCMExt F E σ) (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) (hθ : ∀ w, θ w * C w = C w * Jm R S)
    (k : UG (cA σ) J) (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hkθ : ∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) :
    ∃ γ ∈ RLines σ J, ∃ Y : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ, IsGen τ C γ Y ∧ (∀ w, Y w ∈ upq R S) ∧
      (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k := by
  open GlobalTheory.RealLift.KLineProof in
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Matrix (Ix R S) (Ix R S) ℂ, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    refine GlobalTheory.RealLift.KLineProof.exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_
      (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, GlobalTheory.RealLift.KLineProof.map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := _root_.GlobalTheory.RealLift.exists_line_of_upq F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  refine ⟨γ, hγ, Y, hgen, fun w => (hY w).1, fun w => (hY w).2.1, ?_⟩
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, (hY w).2.2] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.KStableSums
