import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PrimitiveExponentPullback
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.TripleCompare

section Cech

variable {X Y Z : Scheme.{0}}

theorem gen_refine {A B : LB Y} (n : ℤ) (σ : B.ι → A.ι) (hle : ∀ i, B.U i ≤ A.U (σ i))
    (hg : ∀ i j, B.g i j = res (inf_le_inf (hle i) (hle j)) (A.g (σ i) (σ j)) ^ n)
    (h : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen B, t.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun i => res (hle i) (t.s (σ i)) ^ n⟩, fun i j => ?_⟩
  have e := congrArg (res (inf_le_inf (hle i) (hle j))) (ht (σ i) (σ j))
  rw [map_mul, DVR.res_res', DVR.res_res'] at e
  rw [hg, map_zpow, map_zpow, DVR.res_res', DVR.res_res', ← mul_zpow]
  exact congrArg (· ^ n) e

theorem div_g_res (M L : LB Y) (p q : M.ι × L.ι) {V : Y.Opens}
    (h : V ≤ (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) (h₁ : V ≤ M.U p.1 ⊓ M.U q.1)
    (h₂ : V ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div M L).g p q) = res h₁ (M.g p.1 q.1) * (res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (DVR.res_res' _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (DVR.res_res' _ _ _))))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sum_g_res (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K' ⊕ K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L (Sum.elim φ' φ) j ⊓ LB.wchart L (Sum.elim φ' φ) j')
    (h₁ : V ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl))
    (h₂ : V ≤ LB.wchart L φ (j ∘ Sum.inr) ⊓ LB.wchart L φ (j' ∘ Sum.inr)) :
    res h ((LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)).g j j') =
      res h₁ ((LB.LinComb L φ' ε').g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        (res h₂ ((LB.LinComb L φ ε).g (j ∘ Sum.inr) (j' ∘ Sum.inr)))⁻¹ := by
  rw [DVR.linComb_g_res, DVR.linComb_g_res, DVR.linComb_g_res, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp]

theorem wchart_sum (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j =
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := by
  refine le_antisymm (fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩) fun y hy => ?_
  refine Set.mem_iInter.2 fun k => ?_
  rcases k with k | k
  · exact Set.mem_iInter.1 hy.1 k
  · exact Set.mem_iInter.1 hy.2 k

theorem lbIso_iff_gen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    Geo.Tor.LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  constructor
  · refine gen_refine (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun j => (j ∘ Sum.inl, j ∘ Sum.inr)) (fun j => (wchart_sum φ φ' j).le) fun j j' => ?_
    have a := (wchart_sum φ φ' j).le
    have b := (wchart_sum φ φ' j').le
    refine (DVR.res_refl' _).symm.trans ((sum_g_res φ ε φ' ε' j j' le_rfl
      (inf_le_inf (a.trans inf_le_left) (b.trans inf_le_left))
      (inf_le_inf (a.trans inf_le_right) (b.trans inf_le_right))).trans (Eq.symm ?_))
    exact (zpow_one _).trans (div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) _ _ _ _ _)
  · refine gen_refine (B := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun p => Sum.elim p.1 p.2) (fun p => (wchart_sum φ φ' (Sum.elim p.1 p.2)).ge) fun p q => ?_
    refine (DVR.res_refl' _).symm.trans ((div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    exact (zpow_one _).trans (sum_g_res φ ε φ' ε' (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) _ _ _)

theorem wchart_id (L : LB X) (j : PUnit.{1} → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j = L.U (j ⟨⟩) :=
  le_antisymm (fun _ hy => Set.mem_iInter.1 hy PUnit.unit) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_id_g_res (L : LB X) (j j' : PUnit.{1} → L.ι) {V : X.Opens}
    (h : V ≤ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j ⊓ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j')
    (h' : V ≤ L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩)) :
    res h ((L.pull (𝟙 X)).g j j') = res h' (L.g (j ⟨⟩) (j' ⟨⟩)) := by
  rw [DVR.linComb_g_res, Fintype.prod_unique, zpow_one, DVR.tr_def L (ψ := 𝟙 X) h']
  exact DVR.pullU_of_eq_id _ rfl _ _ _ _ _

theorem lbIso_iff_pull_id (L M : LB X) :
    Geo.Tor.LBIso L M ↔ Geo.Tor.LBIso M (L.pull (𝟙 X)) := by
  constructor
  · refine gen_refine (A := LB.div M L) (B := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (p.2, p.1 ⟨⟩))
      (fun p => le_inf inf_le_right (inf_le_left.trans (wchart_id L p.1).le)) fun p q => ?_
    have a := (wchart_id L p.1).le
    have b := (wchart_id L q.1).le
    refine (DVR.res_refl' _).symm.trans ((div_g_res (L.pull (𝟙 X)) M p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res M L (p.2, p.1 ⟨⟩) (q.2, q.1 ⟨⟩) _
      (inf_le_inf inf_le_right inf_le_right)
      (inf_le_inf (inf_le_left.trans a) (inf_le_left.trans b)))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) ((inv_inv _).trans ?_) rfl)
    exact (pull_id_g_res L p.1 q.1 _ _).symm
  · refine gen_refine (B := LB.div M L) (A := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (fun _ => p.2, p.1))
      (fun p => le_inf (inf_le_right.trans (wchart_id L fun _ => p.2).ge) inf_le_left) fun p q => ?_
    have a := (wchart_id L fun _ => p.2).ge
    have b := (wchart_id L fun _ => q.2).ge
    refine (DVR.res_refl' _).symm.trans ((div_g_res M L p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res (L.pull (𝟙 X)) M (fun _ => p.2, p.1)
      (fun _ => q.2, q.1) _ (inf_le_inf (inf_le_right.trans a) (inf_le_right.trans b))
      (inf_le_inf inf_le_left inf_le_left))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) (inv_inv _) (congrArg (·⁻¹) ?_))
    exact pull_id_g_res L (fun _ => p.2) (fun _ => q.2) _ _

end Cech

end GlobalTheory.TripleCompare
