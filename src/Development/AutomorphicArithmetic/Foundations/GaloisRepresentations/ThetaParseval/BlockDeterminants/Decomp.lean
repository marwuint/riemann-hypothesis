import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

open GlobalTheory.ThK.Dbl.Euler (cut cut_mul cut_form cut_sub cut_eq cut_one mm cont_mat prj)

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k]

private theorem cut_add {a b : S} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (A : Matrix k k R) :
    cut a A * cut b A = cut (a + b) A := by
  have h0 : b * a = 0 := by rw [mul_comm]; exact hab
  have h1 : (1 - b) * (1 - a) = 1 - (a + b) := by linear_combination hab
  have h2 : b * (1 - a) = b := by linear_combination -hab
  have h3 : (1 - b) * a = a := by linear_combination -hab
  simp only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h0, h1, h2, h3, zero_smul, add_zero,
    Matrix.one_mul, Matrix.mul_one, add_smul]
  abel

private theorem cut_self (A : Matrix k k R) : cut (1 : S) A = A := by simp [cut]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

private def pr (e : AF F) (he : e * e = e) : UA σ X.J →* UA σ X.J :=
  MonoidHom.mk' (fun g => ⟨⟨cut e (mat g), cut e (mat g⁻¹),
    by rw [cut_mul he, ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul he, ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form he _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul he _ _).symm)

private theorem mat_pr {e : AF F} (he : e * e = e) (g : UA σ X.J) : mat (pr e he g) = cut e (mat g) := rfl

private theorem pr_eq {e : AF F} {he : e * e = e} {g : UA σ X.J} : pr e he g = g ↔ e • (mat g - 1) = mat g - 1 :=
  ⟨fun h => cut_eq.1 (congrArg mat h), fun h => Subtype.ext (Units.ext (cut_eq.2 h))⟩

private theorem pr_one {e : AF F} {he : e * e = e} {g : UA σ X.J} (h : e • (mat g - 1) = 0) : pr e he g = 1 := by
  refine Subtype.ext (Units.ext (sub_eq_zero.1 ?_))
  exact (cut_sub (mat g)).trans h

private theorem cont_pr {e : AF F} (he : e * e = e) : Continuous (pr e he : UA σ X.J → UA σ X.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ X.J => cut e (mat g) := by
    have := cont_mat (σ := σ) (Y := X)
    unfold cut
    refine continuous_matrix fun i j => ?_
    have := this.matrix_elem i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have c2 : Continuous fun g : UA σ X.J => cut e (mat g⁻¹) := c1.comp continuous_inv
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c2⟩) _

private theorem eps_sq : realAd F 1 * realAd F 1 = realAd F 1 :=
  Prod.ext (by
    change (realAd F 1).1 * (realAd F 1).1 = (realAd F 1).1
    rw [PositivityTheory.ThKG.Loc.Bump.eps_fst, one_mul]) (by
    change (realAd F 1).2 * (realAd F 1).2 = (realAd F 1).2
    rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

private theorem pr_one_of {e f : AF F} {he : e * e = e} (h : e * f = 0) {g : UA σ X.J} (hg : f • (mat g - 1) = mat g - 1) :
    pr e he g = 1 :=
  pr_one (by rw [← hg, smul_smul, h, zero_smul])

private theorem pr_fix {e : AF F} (he : e * e = e) (g : UA σ X.J) :
    e • (mat (pr e he g) - 1) = mat (pr e he g) - 1 := by
  rw [mat_pr, cut_sub, smul_smul, he]

private theorem prod_equiv {P Q R : Subgroup (UA σ X.J)} {a b c : AF F} (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (hs : a + b + c = 1) (hP : ∀ g, g ∈ P ↔ a • (mat g - 1) = mat g - 1)
    (hQ : ∀ g, g ∈ Q ↔ b • (mat g - 1) = mat g - 1) (hR : ∀ g, g ∈ R ↔ c • (mat g - 1) = mat g - 1) :
    ∃ j : P × Q × R ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1 := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  have hd : (a + b) * (a + b) = a + b := by linear_combination ha + hb + 2 * hab
  have hdc : (a + b) * c = 0 := by linear_combination hac + hbc
  let φ : UA σ X.J ≃ₜ* P × Q × R :=
    { toFun := fun g => (⟨pr a ha g, (hP _).2 (pr_fix ha g)⟩, ⟨pr b hb g, (hQ _).2 (pr_fix hb g)⟩,
        ⟨pr c hc g, (hR _).2 (pr_fix hc g)⟩)
      invFun := fun x => x.1.1 * x.2.1.1 * x.2.2.1
      left_inv := fun g => Subtype.ext (Units.ext (show cut a (mat g) * cut b (mat g) * cut c (mat g) = mat g by
        rw [cut_add ha hb hab, cut_add hd hc hdc, hs, cut_self]))
      right_inv := fun x => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := x
        have p1 := (hP p).1 hp
        have q1 := (hQ q).1 hq
        have r1 := (hR r).1 hr
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · change pr a ha (p * q * r) = p
          rw [map_mul, map_mul, pr_eq.2 p1, pr_one_of hab q1, pr_one_of hac r1, mul_one, mul_one]
        · change pr b hb (p * q * r) = q
          rw [map_mul, map_mul, pr_eq.2 q1, pr_one_of hba p1, pr_one_of hbc r1, mul_one, one_mul]
        · change pr c hc (p * q * r) = r
          rw [map_mul, map_mul, pr_eq.2 r1, pr_one_of hca p1, pr_one_of hcb q1, one_mul, one_mul]
      map_mul' := fun g h => Prod.ext (Subtype.ext (map_mul _ _ _)) (Prod.ext (Subtype.ext (map_mul _ _ _))
        (Subtype.ext (map_mul _ _ _)))
      continuous_toFun := ((cont_pr ha).subtype_mk _).prodMk (((cont_pr hb).subtype_mk _).prodMk ((cont_pr hc).subtype_mk _))
      continuous_invFun := ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)) }
  exact ⟨φ.symm, fun x => rfl⟩

end UpperTheory.TP

