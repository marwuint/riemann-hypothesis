import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.div {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') :
    Refines (LB.div M M') L (Sum.elim φ φ') (Sum.elim ε fun k => - ε' k) := by
  obtain ⟨σ, le, hg⟩ := h
  obtain ⟨σ', le', hg'⟩ := h'
  refine ⟨fun p => Sum.elim (σ p.1) (σ' p.2), fun p y hy => Set.mem_iInter.2 ?_, fun Z r z p q hp hq => ?_⟩
  · rintro (k | k)
    exacts [Set.mem_iInter.1 (le _ hy.1) k, Set.mem_iInter.1 (le' _ hy.2) k]
  · refine (gm_div M' M r z p q ⟨hp, hq⟩).trans ?_
    rw [hg Z r z _ _ hp.1 hq.1, hg' Z r z _ _ hp.2 hq.2, trF, trF, trF, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rfl

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem Refines.exists_gen (hL : L.IsLB) {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) :
    ∃ s : LB.Gen M, s.IsGen := by
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL hF t ht
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨⟨fun i => res (le i) (u.s (σ i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (gen_trans hu (𝟙 Y) y (le i hy.1) (le j hy.2)))).trans
    (Eq.symm ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hg _ _ y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

end Refine

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

variable {q a p}

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

end GlobalTheory.GtCoordCompare
