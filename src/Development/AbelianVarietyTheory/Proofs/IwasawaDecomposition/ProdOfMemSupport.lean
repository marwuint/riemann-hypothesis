import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt

noncomputable section

namespace GlobalTheory.KerRescale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

theorem card_eq_sum_colLen (μ : YoungDiagram) : μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have hmap : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (0, c.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
    exact YoungDiagram.mem_iff_lt_rowLen.1 h2
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun c hc => hmap c hc),
    Fin.sum_univ_eq_sum_range (fun c => μ.colLen c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

section Hom

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) {K : Type} [CommMonoid K] (a : Lt → K)

def wt : KM.XZ Lt N0 N1 → Additive K := Sum.elim (fun _ => 0) (fun z => Additive.ofMul (a z.1))

theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.minorXZ N0 N1 s p I) (p • Additive.ofMul (a s)) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (KM.XZ Lt N0 N1) ℤ) (Additive.ofMul (a s)) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold KM.minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => Additive.ofMul (a s))
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Gxz_hom (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.Gxz N0 N1 nu I) (∑ s, (nu s).card • Additive.ofMul (a s)) := by
  unfold KM.Gxz
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun s _ => ?_
  rw [card_eq_sum_colLen, Finset.sum_smul]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun c _ => minorXZ_hom N0 N1 a s _ (I s c)

theorem prod_of_mem_support (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) (μ : KM.XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (KM.Gxz N0 N1 nu I).support) :
    ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun z n => a z.1 ^ n) = ∏ s, a s ^ (nu s).card := by
  have h := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hμ' : μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
    ext x; cases x <;> simp
  rw [hμ', Finsupp.weight_apply, Finsupp.sum_sumElim] at h
  generalize Finsupp.sumFinsuppEquivProdFinsupp μ = p at h ⊢
  have h2 := congrArg Additive.toMul h
  unfold Finsupp.sum at h2
  simp only [Function.comp_apply, wt, Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, toMul_sum,
    toMul_nsmul, toMul_ofMul] at h2
  exact h2

end Hom

theorem applyAt0_rescale {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime] (a : Lt → ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    KM.applyAt0 N0 N1 l (MvPowerSeries.rescale (fun z => a z.1) Th) (KM.Gxz N0 N1 nu I) =
      (∏ s, a s ^ (nu s).card) • KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I) := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [MvPowerSeries.coeff_rescale, prod_of_mem_support N0 N1 a nu I μ hμ, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem rescale_atLin {σ κ : Type} [Finite σ] [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (a : κ → ℂ_[p])
    (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rescale a (atLin c (fun j => MvPowerSeries.X j) F) =
      atLin (fun k j => a j * c k j) (fun j => MvPowerSeries.X j) F := by
  unfold atLin
  have hs : MvPowerSeries.HasSubst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * MvPowerSeries.X j) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => ?_
    simp [map_sum]
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hs (MvPowerSeries.HasSubst.smul_X a)]
  congr 1
  funext k
  rw [← MvPowerSeries.rescale_eq_subst, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← MvPowerSeries.rescaleAlgHom_apply, map_smul, MvPowerSeries.rescaleAlgHom_apply,
    MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X a)]
  show c k j • (a j • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])) = (a j * c k j) • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])
  rw [mul_comm, mul_smul]

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D}
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem tauEmb_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (x : D.host.E) : ∃ y : D.what₂.LL, tauEmb D (P.lam w) τ x = P.iL w y := by
  have e : D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) = embT D τ x := RingHom.congr_fun D.embE_φ₀ _
  refine ⟨D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x), ?_⟩
  rw [P.iL_lam, e]
  rfl

def adUnit (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Cw D w :=
  if AdPl D w then (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ else 1

theorem norm_adUnit (hU : DgenUnitAd P O) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) :
    ‖adUnit P O w u μ τ‖ = 1 := by
  unfold adUnit
  split_ifs with hw
  · rw [norm_inv, hU w hw u μ τ, inv_one]
  · exact norm_one

end GlobalTheory.KerRescale

end
