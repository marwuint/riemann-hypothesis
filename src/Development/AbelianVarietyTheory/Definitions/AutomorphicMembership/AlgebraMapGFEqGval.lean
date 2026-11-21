import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG ZhatOM IsInCell ptMat)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS)

namespace GlobalTheory.IntTerm

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {A : Matrix (Fin S.rank) (Fin (r + 1)) E}

def colVec (S : HSpace E) {a : Type} (A : Matrix (Fin S.rank) a E) (b : a) : S.V :=
  S.frame.equivFun.symm fun i => A i b

theorem coMat_colVec {a : Type} (A : Matrix (Fin S.rank) a E) : coMat S (colVec S A) = A := by
  ext i b
  exact congrFun (S.frame.equivFun.apply_symm_apply fun i => A i b) i

def lflagOf (h : IsFrame (starRingEnd E) S.gram T A) : LFlag S r T :=
  have k (a b : Fin (r + 1)) : S.hT (colVec S A a) (colVec S A b) = TF r T a b := by
    rw [← h.2]
    conv_rhs => rw [← coMat_colVec A, pairM_coMat]
    rfl
  { fl :=
      { e := fun a => colVec S A a.castSucc
        z := colVec S A (Fin.last r)
        e_indep := by
          refine LinearIndependent.comp (v := colVec S A) ?_ _ (Fin.castSucc_injective r)
          refine LinearIndependent.map' (v := A.col) ?_ _ S.frame.equivFun.symm.ker
          obtain ⟨L, hL⟩ := h.1
          refine Matrix.mulVec_injective_iff.1 fun c d e => ?_
          simpa [Matrix.mulVec_mulVec, hL] using congrArg (L *ᵥ ·) e
        e_iso := fun a b => by rw [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
        z_orth := fun a => by rw [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
        z_norm := by rw [k]; simp [TF] }
    zt := colVec S A (Fin.last r) }

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word}

def fixedFlag (D : D7) (u : D.what₂.Word) : LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E) :=
  lflagOf (S := hS D) (isFrame_recFrame D u)

theorem fixedFlag_eq_lf (D : D7) (u : D.what₂.Word) : fixedFlag D u = Formalism.MainNotions.S.lf D (fixedFlag D u).fl := rfl

namespace RecTerm

end RecTerm

namespace RecTerm

end RecTerm

end Record

end GlobalTheory.IntTerm
