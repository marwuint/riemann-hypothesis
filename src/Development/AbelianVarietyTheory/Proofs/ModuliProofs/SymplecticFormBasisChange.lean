import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelOfTheta

open GlobalTheory.CechPic

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified A L) (T : Over S) :
    pull (1 : T ⟶ A).left (cls L hL) = 0 := by
  have e : pull (eSec A) (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  have e' : (1 : T ⟶ A).left = (toUnit T).left ≫ eSec A := rfl
  rw [e', pull_comp, e, map_zero]

omit [GrpObj A] in
theorem pull_pull {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ A) (c : Pic A.left) :
    pull f.left (pull a.left c) = pull (f ≫ a).left c := (pull_comp _ _ _).symm

variable [IsCommMonObj A]

theorem isLB_lam (hL : L.IsLB) : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam (hL : L.IsLB) :
    cls _ (isLB_lam hL) = pull (fst A A * snd A A).left (cls L hL) - pull (fst A A).left (cls L hL) -
      pull (snd A A).left (cls L hL) + pull (1 : A ⊗ A ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ (isLB_lam hL)).trans ?_
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum A (x2 A) I).left (cls L hL)) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have p₀ : psum A (x2 A) ∅ = 1 := rfl
  have p₁ : psum A (x2 A) {0} = fst A A := _root_.mul_one (fst A A)
  have p₂ : psum A (x2 A) {1} = snd A A := _root_.mul_one (snd A A)
  have p₃ : psum A (x2 A) {0, 1} = fst A A * snd A A := congrArg (fst A A * ·) (_root_.mul_one (snd A A))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem pull_lam (hL : L.IsLB) (hr : Out.Rigidified A L) {T : Over S} (a b : T ⟶ A) :
    pull (lift a b).left (cls _ (isLB_lam hL)) =
      pull (a * b).left (cls L hL) - pull a.left (cls L hL) - pull b.left (cls L hL) := by
  rw [cls_lam hL, pull_one hL hr, add_zero, map_sub, map_sub, pull_pull, pull_pull, pull_pull, MonObj.comp_mul,
    lift_fst, lift_snd]

end Classes

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L M : LB A.left}

theorem exists_theta_iff (hL : L.IsLB) (k : ℤ) {T : Over S} (x : T ⟶ A) :
    (∃ θ : Out.ThetaGrp A L k T, θ.pt = x) ↔
      k • pull (snd T A).left (cls L hL) - k • pull (Out.translPt A x).left (cls L hL) = 0 := by
  have e := cls_linComb hL (K := Fin 2) ![(snd T A).left, (Out.translPt A x).left] ![k, -k] (LB.isLB_linComb hL _ _)
  rw [Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, ← sub_eq_add_neg] at e
  rw [← e, cls_eq_zero_iff]
  exact ⟨fun ⟨θ, h⟩ => h ▸ ⟨θ.φ, θ.isGen⟩, fun ⟨t, ht⟩ => ⟨⟨x, t, ht⟩, rfl⟩⟩

theorem weilIs_of_pow (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (d : ℕ)
    (e : cls M hM = d • cls L hL) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L k x y c) : Out.WeilIs A M k x y (c ^ d) := by
  have up : ∀ (T' : Over S) (u : T' ⟶ A), (∃ θ : Out.ThetaGrp A L k T', θ.pt = u) →
      ∃ θ : Out.ThetaGrp A M k T', θ.pt = u := fun T' u H => by
    rw [exists_theta_iff hL] at H
    rw [exists_theta_iff hM, e, map_nsmul, map_nsmul, smul_comm k d, smul_comm k d, ← smul_sub, H, smul_zero]
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := k) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, H, -⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, H⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
  have iso : LBIso (lbPow L d) (M.pull (𝟙 A : A ⟶ A).left) :=
    (cls_eq_iff (isLB_lbPow hL d) (pull_isLB hM _)).1 (by
      rw [cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e])
  have := (weilIs_along_hom hG S A A (𝟙 A) L M d k T x y c c' hA hA hL hM inferInstance iso
    (by simpa using hc')).2 h
  exact this ▸ hc'

end Pairing

section Principal

variable {S : Scheme.{0}}

theorem cls_diag (hG : Out.GlobalFnsSt)
    (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (P : Out.PolAV S) [IsCommMonObj P.A] :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2
    ((MulPull.mulPull_of_cube_of_symm hc (exists_gen_negLB hG)).1 S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h
  have e : Out.mulA P.A 2 = 𝟙 P.A * 𝟙 P.A := pow_two _
  rw [e] at h
  rw [cls_pull (isLB_lam P.isLB), pull_lam P.isLB P.rigid, Over.id_left, pull_id]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  push_cast
  module

theorem relAmple_of_pow {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A L) : Out.RelAmple A M := by
  have := hA.proper
  rw [relAmple_iff_isAmpleLB A hL] at h
  refine relAmple_of_isAmpleLB A hM fun U hU => ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _) ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).1
    ((isAmpleLB_pow_iff (pull_isLB hL _) hd).2 (h U hU))
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end Principal

end GlobalTheory.SiegelOfTheta
