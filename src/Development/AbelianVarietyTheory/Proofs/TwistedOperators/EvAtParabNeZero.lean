import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

abbrev LiftSp (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Type :=
  IndSp (part r t) ((extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)).comp
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)

def evAt (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) (g : GL (Fin (r + t)) k) :
    LiftSp t σ χW χV →ₗ[ℂ] V where
  toFun f := TensorProduct.rid ℂ V (f.1.1 g)
  map_add' f f' := map_add (TensorProduct.rid ℂ V) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := map_smul (TensorProduct.rid ℂ V) c (f.1.1 g)

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

theorem evAt_apply (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g f = TensorProduct.rid ℂ V (f.1.1 g) := rfl

theorem evAt_lift (g x : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g (liftRep t σ χW χV x f) = evAt t σ χW χV (g * x) f := rfl

def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)

end Local

end GlobalTheory.TypeDim
