import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.HomExtDvrSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section DivPull

variable {X Y : Scheme.{0}}

theorem mem_pull_iff {M : LB X} (f : Y ⟶ X) (j : PUnit → M.ι) (y : Y) :
    y ∈ (M.pull f).U j ↔ f y ∈ M.U (j ⟨⟩) := ⟨fun h => Set.mem_iInter.1 h ⟨⟩, fun h => Set.mem_iInter.2 fun ⟨⟩ => h⟩

private theorem pullU_res_eq_res_preimage_mono {A B : Scheme.{0}} (g : A ⟶ B) {U V : B.Opens} (h : V ≤ U) (u : Γ(B, U)ˣ) :
    pullU g V (res h u) = res (g.preimage_mono h) (pullU g U u) := by
  apply Units.ext
  have := congrArg (fun φ => φ.hom u.val) (g.naturality (homOfLE h).op)
  simpa [pullU, res] using this

private theorem res_res_eq_res_trans' {Z : Scheme.{0}} {U V W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(Z, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  apply Units.ext
  first
    | (simp [res]; done)
    | (simp only [res, Units.coe_map, MonoidHom.coe_coe]
       rw [← CommRingCat.comp_apply, ← Functor.map_comp]
       rfl)

private theorem pull_U_inf_le_preimage_inf {P : LB X} (f : Y ⟶ X) (j j' : PUnit → P.ι) :
    (P.pull f).U j ⊓ (P.pull f).U j' ≤ f ⁻¹ᵁ (P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩)) :=
  fun y hy => show f y ∈ P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩) from
    Opens.mem_inf.2 ⟨(mem_pull_iff f j y).1 (Opens.mem_inf.1 hy).1,
      (mem_pull_iff f j' y).1 (Opens.mem_inf.1 hy).2⟩

private theorem pull_g_eq_res_pullU_g {P : LB X} (f : Y ⟶ X) (j j' : PUnit → P.ι)
    (hle : (P.pull f).U j ⊓ (P.pull f).U j' ≤ f ⁻¹ᵁ (P.U (j ⟨⟩) ⊓ P.U (j' ⟨⟩))) :
    (P.pull f).g j j' = res hle (pullU f _ (P.g (j ⟨⟩) (j' ⟨⟩))) := by
  show (∏ _k : PUnit, _) = _
  simp only [zpow_one]
  exact Fintype.prod_unique _

end DivPull

section RigPull

open MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

private theorem pullU_pullU_eq_pullU_comp {X Y Z : Scheme.{0}} (b : Z ⟶ Y) (a : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    pullU b (a ⁻¹ᵁ W) (pullU a W u) = pullU (b ≫ a) W u := by
  apply Units.ext
  first
    | (simp [pullU]; done)
    | (simp [pullU]; rfl)
    | rfl

private theorem res_pullU_eq_of_eq {P Z : Scheme.{0}} (C C' : P ⟶ Z) (h : C = C') (W : Z.Opens) (u : Γ(Z, W)ˣ)
    {V : P.Opens} (k : V ≤ C ⁻¹ᵁ W) (k' : V ≤ C' ⁻¹ᵁ W) :
    res k (pullU C W u) = res k' (pullU C' W u) := by
  subst h
  rfl

private theorem res_pullU_pullU_eq_of_comp_eq {P Q Q' Z : Scheme.{0}} (A : P ⟶ Q) (B : Q ⟶ Z) (A' : P ⟶ Q') (B' : Q' ⟶ Z)
    (h : A ≫ B = A' ≫ B') (W : Z.Opens) (u : Γ(Z, W)ˣ) {V : P.Opens}
    (k : V ≤ A ⁻¹ᵁ (B ⁻¹ᵁ W)) (k' : V ≤ A' ⁻¹ᵁ (B' ⁻¹ᵁ W)) :
    res k (pullU A _ (pullU B W u)) = res k' (pullU A' _ (pullU B' W u)) := by
  rw [pullU_pullU_eq_pullU_comp, pullU_pullU_eq_pullU_comp]
  exact res_pullU_eq_of_eq _ _ h _ _ _ _

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  have hV : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
      e ⁻¹ᵁ ((L.pull (eSec G)).U (fun _ => i ⟨⟩ ⟨⟩) ⊓ (L.pull (eSec G)).U (fun _ => j ⟨⟩ ⟨⟩)) :=
    le_inf (inf_le_left.trans (rigPull_le F e he L i)) (inf_le_right.trans (rigPull_le F e he L j))
  have hr' := congrArg (fun x => res hV (pullU e _ x)) (hr (fun _ => i ⟨⟩ ⟨⟩) (fun _ => j ⟨⟩ ⟨⟩))
  simp only [map_mul, pullU_res_eq_res_preimage_mono, res_res_eq_res_trans'] at hr'
  have hG : res hV (pullU e _ ((L.pull (eSec G)).g (fun _ => i ⟨⟩ ⟨⟩) (fun _ => j ⟨⟩ ⟨⟩))) =
      ((L.pull F).pull (eSec G')).g i j := by
    rw [pull_g_eq_res_pullU_g (P := L) (eSec G) _ _ (pull_U_inf_le_preimage_inf (P := L) (eSec G) _ _), pullU_res_eq_res_preimage_mono, res_res_eq_res_trans',
      pull_g_eq_res_pullU_g (P := L.pull F) (eSec G') i j (pull_U_inf_le_preimage_inf (P := L.pull F) (eSec G') i j),
      pull_g_eq_res_pullU_g (P := L) F (i ⟨⟩) (j ⟨⟩) (pull_U_inf_le_preimage_inf (P := L) F (i ⟨⟩) (j ⟨⟩)), pullU_res_eq_res_preimage_mono, res_res_eq_res_trans']
    exact res_pullU_pullU_eq_of_comp_eq e (eSec G) (eSec G') F he.symm _ _ _ _
  rw [hG] at hr'
  first
    | (erw [← res_res_eq_res_trans' (rigPull_le F e he L i)
          (inf_le_left : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
            ((L.pull F).pull (eSec G')).U i),
        ← res_res_eq_res_trans' (rigPull_le F e he L j)
          (inf_le_right : ((L.pull F).pull (eSec G')).U i ⊓ ((L.pull F).pull (eSec G')).U j ≤
            ((L.pull F).pull (eSec G')).U j)] at hr'
       exact hr')
    | (refine (res_res_eq_res_trans' _ _ _).trans (hr'.trans ?_)
       exact congrArg (fun x => _ * x) (res_res_eq_res_trans' _ _ _).symm)

end RigPull

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
