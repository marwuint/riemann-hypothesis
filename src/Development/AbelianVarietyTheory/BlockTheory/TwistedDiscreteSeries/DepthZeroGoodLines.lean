import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))

def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)

variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]

def liftRep (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) :=
  prod₂ (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
