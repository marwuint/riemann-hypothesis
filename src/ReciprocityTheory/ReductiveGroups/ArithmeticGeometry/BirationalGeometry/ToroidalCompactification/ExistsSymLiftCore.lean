import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section GV

variable {X Y Y' : Scheme.{0}} (M : LB X)

def GV (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb M φ ε)), u.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ Z r z J, Good M z J → val u r z J = v Z r z J

variable {M} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} {v v'}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  first
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
    | (rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    | simp [← Functor.map_comp_apply]
    | simp

private lemma isGen_mulGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro j j'
  have hl : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ (i ∘ Sum.inl) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have hr : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ' (i ∘ Sum.inr) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have e1 := congrArg (res (inf_le_inf (hl j) (hl j'))) (ht (j ∘ Sum.inl) (j' ∘ Sum.inl))
  have e2 := congrArg (res (inf_le_inf (hr j) (hr j'))) (ht' (j ∘ Sum.inr) (j' ∘ Sum.inr))
  erw [map_mul, res_res_lemma, res_res_lemma] at e1
  erw [map_mul, res_res_lemma, res_res_lemma] at e2
  have hg : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g j j' =
      res (inf_le_inf (hl j) (hl j')) ((LB.LinComb L φ ε).g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        res (inf_le_inf (hr j) (hr j')) ((LB.LinComb L φ' ε').g (j ∘ Sum.inr) (j' ∘ Sum.inr)) := by
    dsimp only [LB.LinComb]
    rw [Fintype.prod_sum_type]
    erw [map_prod, map_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_) <;>
      erw [map_zpow, res_res_lemma] <;> rfl
  dsimp only [LB.mulGen]
  erw [map_mul, map_mul, res_res_lemma, res_res_lemma, res_res_lemma, res_res_lemma, e1, e2, hg]
  exact mul_mul_mul_comm _ _ _ _

private lemma isGen_invGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    (LB.invGen L φ ε t).IsGen := by
  intro i i'
  have hg : (LB.LinComb L φ fun k => -ε k).g i i' = ((LB.LinComb L φ ε).g i i')⁻¹ := by
    dsimp only [LB.LinComb]
    simp only [zpow_neg, Finset.prod_inv_distrib] <;> rfl
  dsimp only [LB.invGen]
  erw [map_inv, map_inv, ht i i', mul_inv, hg]
  rfl

theorem GV.mul (a : GV M F v) (b : GV M F' v') :
    GV M (fun U _ h => F U h * F' U h) fun Z r z J => v Z r z J * v' Z r z J := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  obtain ⟨K', hK', φ', ε', u', hu', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', LB.mulGen (L := M) φ ε φ' ε' u u',
    isGen_mulGen_of_isGen M φ ε φ' ε' u u' hu hu', ?_, ?_⟩
  · intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hF, hF']
  · intro Z r z J hJ
    rw [val_mul, hv Z r z J hJ, hv' Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.inv (a : GV M F v) : GV M (fun U _ h => (F U h)⁻¹) fun Z r z J => (v Z r z J)⁻¹ := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  refine ⟨K, hK, φ, fun k => -ε k, LB.invGen (L := M) φ ε u, isGen_invGen_of_isGen M φ ε u hu, ?_, ?_⟩
  · intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · intro Z r z J hJ
    rw [val_inv, hv Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.pow (a : GV M F v) (n : ℕ) : GV M (fun U _ h => F U h ^ n) fun Z r z J => v Z r z J ^ n := by
  have key : ∀ {G G' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
      {w w' : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ},
      GV M G w → G = G' → w = w' → GV M G' w' := by
    intro G G' w w' h hG hw
    subst hG
    subst hw
    exact h
  induction n with
  | zero =>
    refine key (a.mul a.inv) ?_ ?_
    · funext U inst h
      exact (mul_inv_cancel _).trans (pow_zero _).symm
    · funext Z r z J
      exact (mul_inv_cancel _).trans (pow_zero _).symm
  | succ n ih =>
    refine key (ih.mul a) ?_ ?_
    · funext U inst h
      exact (pow_succ _ _).symm
    · funext Z r z J
      exact (pow_succ _ _).symm

end GV

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A)
include c hG hA

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
