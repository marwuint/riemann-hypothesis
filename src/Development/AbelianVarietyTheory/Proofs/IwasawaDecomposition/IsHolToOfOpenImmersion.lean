import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorHolo

section Hol

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Z : Scheme.{0}}

theorem isHolTo_of_openImmersion (i : X ⟶ Z) [IsOpenImmersion i] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have hU : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [← ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  exact key U hU f

theorem isHolTo_const {B : Set W} (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B fun _ => x := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa only [h, and_true, Set.ofPred_mem_eq] using hB
  · simpa only [h, and_false, Set.ofPred_false] using isOpen_empty

theorem isHolTo_of_fst {S : Scheme.{0}} (p : X ⟶ Z) (q : S ⟶ Z) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    {y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback p q)} (s : Sp ℂ ⟶ S) (hs : ∀ b, y b ≫ pullback.snd _ _ = s)
    (h : IsHolTo B fun b => y b ≫ pullback.fst _ _) : IsHolTo B y := by
  have he : ∀ b, (y b ≫ pullback.fst p q) ≫ p = s ≫ q := fun b => by
    rw [← hs b, Category.assoc, Category.assoc, pullback.condition]
  refine LocLift.isHolTo_congr (holPair _ _ _ p q n B _ (fun _ => s) he hB h (isHolTo_const hB s)) fun b _ => ?_
  exact pullback.hom_ext (pullback.lift_fst _ _ _).symm ((hs b).trans (pullback.lift_snd _ _ _).symm)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousOn_of_isHolTo {B : Set W} {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem differentiableAt_chart {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1)
    (ch : AlgChart p σ D) {b : W} (hb : b ∈ B) (hy : y b ∈ ch.e.source) :
    DifferentiableAt ℂ (fun v => ch.e (y v)) b := by
  refine (differentiableAt_piLp 2).2 fun a => ?_
  have h1 := ((h ch.U (ch.x a)).2).differentiableAt ((h ch.U (ch.x a)).1.mem_nhds ⟨hb, ch.source_subset hy⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).preimage_mem_nhds
    (ch.e.open_source.mem_nhds hy)] with v hv
  exact ch.apply_eq _ hv a

theorem isHolTo_symm (ch : AlgChart p σ D) : IsHolTo ch.e.target fun v => (ch.e.symm v).1 := fun U f =>
  ⟨ChartGlue.isOpen_over ch.e (isOpen_ptsIn U), ch.holo U f⟩

end Hol

section Frames

open GlobalTheory.TorsionHolomorphic ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (X : Data E r) {B : Set W}

theorem differentiableOn_perFr {x : W → Frame X.Ψ r} (hx : ∀ b ∈ B, x b ∈ X.dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    DifferentiableOn ℂ (fun b => perFr X (x b) v τ i) B := by
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun a _ =>
      (differentiableOn_matrix_inv _ B (hd _) (fun b hb => (hx b hb _).1) _ _).mul_const _
  · exact differentiableOn_const _
  · simp only [hermC]
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun c _ =>
      ((hd _ _ _).mul_const _).mul_const _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem differentiable_stdMat [Fintype Tau] (hj : j ≤ r) (κ : Tau ≃ X.Ψ) (τ : X.Ψ) (a c : Fin r) :
    Differentiable ℂ fun v => mat (stdMat X hj κ (unflat v)) τ a c := by
  refine differentiableOn_univ.1 (differentiableOn_matrix_mul (fun _ => mat (x0F X) τ)
    (fun v => reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) _
    (fun _ _ => differentiableOn_const _) (fun a c => ?_) a c)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases idx hj a with a | a <;> rcases idx hj c with c | c
  · exact differentiableOn_const _
  · exact differentiableOn_apply (κ.symm τ, a, c) _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Frames

end GlobalTheory.TrueCx.TorHolo
