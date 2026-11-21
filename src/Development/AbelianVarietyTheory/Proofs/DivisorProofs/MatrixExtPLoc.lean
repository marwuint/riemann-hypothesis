import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_ext {a b : FiniteAdeleRing (𝓞 E) E} (h : ∀ v, pLoc E v a = pLoc E v b) : a = b :=
  Subtype.ext (funext h)

theorem matrix_ext_pLoc {A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ v, A.map (pLoc E v) = B.map (pLoc E v)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact pLoc_ext E fun v => congrFun (congrFun (h v) i) j

end GlobalTheory.EulerTw
