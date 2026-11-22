import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
import Formalism.LocalToGlobal.GlobalTheory.PassageBaseSymmetricLevels

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Bridge

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {U : Type} [AddCommGroup U] [Module K U]

theorem epOp_eq_epP (σ : Representation K G U) (P : Subgroup G) (ψ : P →* Kˣ) (χ : P →* (𝓞 K)ˣ)
    (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.epOp σ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.epP P χ σ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp Formalism.IndefR.TransferLatticeStatement.epP
  simp only [hχ]
  congr
  exact Subsingleton.elim _ _

theorem nOf_eq_nS {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.nS τ P χ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.TransferLatticeStatement.nS
  first
  | (unfold Formalism.IndefR.IndefiniteEpsilonOperator.epSp; rw [epOp_eq_epP τ P ψ χ hχ])
  | (simp only [Formalism.IndefR.IndefiniteEpsilonOperator.epSp, epOp_eq_epP τ P ψ χ hχ])
  | (rw [← epOp_eq_epP τ P ψ χ hχ]; rfl)

end Bridge

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

end In

end Formalism.IndefR.CxPass
