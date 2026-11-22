import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.map (pLoc E w) g).1 i j = pLoc E w (g.1 i j) := rfl

theorem loc_inv_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (pLoc E w) g)⁻¹).1 i j = pLoc E w ((g⁻¹).1 i j) := by
  rw [← map_inv]; rfl

theorem gl_ext {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g = Matrix.GeneralLinearGroup.map (pLoc E w) h) :
    g = h :=
  Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w =>
    congrArg (fun x : GLw n w => x.1 i j) (H w)))

theorem mem_KGL_iff {w : Pl E} {x : GLw n w} : x ∈ GlobalTheory.LFun.KGL w n ↔
    (∀ i j, x.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (x⁻¹).1 i j ∈ w.adicCompletionIntegers E :=
  GlobalTheory.AdelicU.mem_GLint_iff

theorem mem_Kglob {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    g ∈ Kglob E n ↔ ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  simp only [Kglob, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem coe_Kglob : (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    (PIW.ClassFinD.KGL E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  ext g
  change g ∈ Kglob E n ↔ PIW.ClassFinD.MatInt g.val ∧ PIW.ClassFinD.MatInt (g⁻¹).val
  rw [mem_Kglob]
  simp only [mem_KGL_iff, loc_val, loc_inv_val]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

theorem isCompact_Kglob : IsCompact (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  rw [coe_Kglob]; exact GlobalTheory.isCompact_KGL E n

theorem isOpen_Kglob : IsOpen (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  have hO : IsOpen ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} := by
    have e : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => M i j) ⁻¹'
          ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) := by
      ext M; simp [PIW.ClassFinD.MatInt]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((continuous_apply j).comp (continuous_apply i))
  rw [coe_Kglob]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage Units.continuous_coe_inv)

theorem mem_orb_iff (u w : Pl E) :
    w ∈ orb E u ↔ w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  rw [orb, Finset.mem_insert, Finset.mem_singleton, GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact GlobalTheory.SplitPts.conjPl_self_conjSrc u
  · have e := eq_conjSrc h
    change w = conjSrc (IsCMField.complexConj E).toRingEquiv u
    rw [e]
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm

end GlobalTheory.EulerTwRestr

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.EulerTwRestr
