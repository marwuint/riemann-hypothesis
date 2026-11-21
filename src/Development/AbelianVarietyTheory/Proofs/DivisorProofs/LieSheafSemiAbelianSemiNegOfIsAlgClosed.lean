import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonpos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonpos

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem exists_isGenOver (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (x : Sp K ⟶ C), IsGenOver k x := by
  have := LieSemineg.isIntegral_curve h.1 h.2.2
  let x : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
  let φ : CommRingCat.of k ⟶ CommRingCat.of C.functionField := Spec.preimage (x ≫ strHom k C)
  refine ⟨C.functionField, inferInstance, φ.hom.toAlgebra, x, h, isGen_fromSpecStalk C, ?_⟩
  exact (Spec.map_preimage (x ≫ strHom k C)).symm

theorem semiNeg_lie_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  intro k _ _ _ C _ h G _ hG W r hW i hi
  obtain ⟨K, _, _, x, hx⟩ := exists_isGenOver k C h
  obtain ⟨V₀, s, g, hV, hs, hg, hl⟩ := _root_.GlobalTheory.Nef.exists_frame_locFrames k K C x hx W r hW
  have hL := _root_.GlobalTheory.Nef.linesLE_zero_of_sub_lie k K C x hx G hG W r i hi V₀ s g hV hs hg hl
  have hd := _root_.GlobalTheory.Nef.deg_le_rank_mul_of_linesLE r k K (_root_.GlobalTheory.Nef.CurveFF.isFF_of_isGenOver k K C x hx) g hg 0 hL
  rw [mul_zero] at hd
  exact _root_.GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos k K C x hx W r hW V₀ s g hV hs hg hl (by exact_mod_cast hd)

end GlobalTheory.Nef
