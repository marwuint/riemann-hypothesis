import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre

noncomputable section

open NumberField MeasureTheory Matrix Polynomial Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspRep.Central
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem commute_Zalg {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X)) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

variable (E) in

def cpowChar (s : ℂ) : HChar E :=
  ⟨MonoidHom.toHomUnits
      { toFun := fun x => Complex.exp (s * Real.log (ideleNorm (E := E) x))
        map_one' := by simp
        map_mul' := fun x y => by
          rw [map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _), ← Complex.exp_add]
          push_cast; ring_nf },
    Units.isEmbedding_val₀.continuous_iff.2 (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ideleNorm.log fun _ => ideleNorm_ne_zero _)))),
    fun k => Units.ext (by
      have h := ideleNorm_principalIdele (E := E) k
      exact (congrArg (fun r : ℝ => Complex.exp (s * Real.log r)) h).trans (by simp))⟩

theorem exists_chiDet_splitCentre (ha : 0 < a) (c : ℂ) :
    ∃ χ : HChar E, ∀ t : ℝ, ((chiDet a χ (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (c * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨cpowChar E (c / D 1), fun t => ?_⟩
  change Complex.exp (c / D 1 * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

end GlobalTheory.CuspQuot

end
