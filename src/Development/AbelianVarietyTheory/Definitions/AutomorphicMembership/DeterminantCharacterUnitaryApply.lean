import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr.DetGroupModel

section General

variable {L : Type} [Field L] [NumberField L]

theorem diag_eq (k : Lˣ) : diagUnits L k = infDiag k * finPartI L (diagUnits L k) := by
  classical
  apply Units.ext
  have h1 : ∀ s : Finset (InfinitePlace L), ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 ∧
      ∀ w', ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w' =
        if w' ∈ s then algebraMap L w'.Completion (k : L) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨rfl, fun _ => rfl⟩
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine ⟨?_, fun w' => ?_⟩
      · show (1 : FiniteAdeleRing (𝓞 L) L) * _ = 1
        rw [one_mul]; exact ih.1
      · show (Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) a (algebraMap L a.Completion (k : L)) w') * _ = _
        rw [ih.2 w']
        by_cases h : w' = a
        · subst h; simp [ha]
        · simp [h]
  have h2 : infDiag k = ∏ w, infIdele L w (atInf w k) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]; rfl
  rw [h2]
  refine Prod.ext (funext fun w => ?_) ?_
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w * 1
    rw [(h1 _).2 w, if_pos (Finset.mem_univ _), mul_one]; rfl
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 * _
    rw [(h1 _).1, one_mul]; rfl

theorem fin_diag (χ : HChar L) (k : Lˣ) : χ.1 (finPartI L (diagUnits L k)) = (χ.inf k)⁻¹ := by
  have h := χ.2.2 k
  rw [diag_eq, map_mul] at h
  exact eq_inv_of_mul_eq_one_right h

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_conj (σ : H.E →+* ℂ) (z : H.E) : σ (H.conj z) = star (σ z) :=
  H.conjE_apply σ z

end GlobalTheory.Mem.Chr.DetGroupModel
