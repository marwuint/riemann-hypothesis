import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemNonzeroLocusOfIsActOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingDetermines

open Out CommutatorPairing DescentPairing PrimCocycle IsoDescent

section OnePoint

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A}

theorem exists_gen_transl (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (cb : CubicalStr A L) {T : Over S} (p₀ : T.left)
    (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * a)).left z J = val u (lift t a).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t a z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t a z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) a (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' a
  have t₂ := hs' ((t ≫ θx.pt) * a)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end OnePoint

section Field

variable {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_lam (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (α : A ⟶ P.A) [IsMonHom α] (d n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L
        (fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (fun I => lamε I * d)),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ α) (y ≫ α) c → ∀ (z : A.left) (J), Good P.L z J →
          val u ((toUnit A ≫ y) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (c ^ d) := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hpow : ∀ y : T ⟶ A, y ^ n = 1 → (y ≫ α) ^ n = 1 := fun y hy => by
    rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ α) (hpow x hx)
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ α).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (ε' := lamε)
    (fun U _ h => by
      have e₀ : mulA A n ≫ lift (toUnit A ≫ x) (𝟙 A) = lift (toUnit A ≫ x) (𝟙 A ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit A) α ≫ mulT P.A T n ≫ translPt P.A (x ≫ α) = ((toUnit A ≫ x) * 𝟙 A ^ n) ≫ α := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd, MonObj.mul_comp,
          MonObj.pow_comp, Category.id_comp, Category.assoc]
      have e₂ : lift (toUnit A) α ≫ snd T P.A ^ n = (𝟙 A ^ n) ≫ α := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit A ≫ (1 : T ⟶ P.A) = (1 : A ⟶ A) ≫ α := by rw [MonObj.comp_one, MonObj.one_comp]
      have e := prod_lam (toUnit A ≫ x) (𝟙 A ^ n) (fun q => h (q ≫ α.left))
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit A) α).left) (LB.pullGen P.L _ _ σ (toUnit A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  obtain ⟨u, hu, v⟩ := WeilIsogeny.exists_gen_pow (ε' := fun I => lamε I * d) d (fun _ => rfl) u₁ hu₁
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have w : ∀ a : A ⟶ A, val u a.left z J =
      (val u₀ (lift (toUnit A) (a ≫ α)).left z J * val σ (toUnit A).left z J) ^ d := fun a => by
    rw [v, v₁ _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ α) c (hpow y hy) hc A (toUnit A) (𝟙 A ≫ α) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 A))).symm)
  rw [MonObj.mul_comp, Category.assoc, map_pow, ← mul_pow, mul_right_comm]
  exact congrArg (fun q => (q * _) ^ d) w₀

theorem exists_gen_axis {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : A.left ⟶ X) (e : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L (fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (fun I => lamε I * e)),
      u.IsGen := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (ε' := fun I => lamε I * e) (fun U _ h => by
      have q := prod_lam (𝟙 A) (1 : A ⟶ A) (fun q => h (q ≫ F) ^ e)
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] at q
      refine (Fintype.prod_empty _).trans (q.symm.trans (Finset.prod_congr rfl fun I _ => ?_))
      rw [← zpow_mul, mul_comm e, Category.assoc]) (LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨u, hu⟩

end Field

end GlobalTheory.PairingDetermines

namespace GlobalTheory

end GlobalTheory
