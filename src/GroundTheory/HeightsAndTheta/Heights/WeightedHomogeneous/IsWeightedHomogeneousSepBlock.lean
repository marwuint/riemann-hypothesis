import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

namespace BlockSurjectivity

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev BlockRing (n : ι → ℕ) (k₀ : ι) : Type := MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ

def sepBlock (k₀ : ι) : MvPolynomial (Coord n) ℤ →ₐ[ℤ] MvPolynomial (Coord n) (BlockRing n k₀) :=
  aeval fun v ↦ if h : v.1 = k₀ then C (X ⟨(), Fin.cast (by rw [h]) v.2⟩) else X v

def evalBlock {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) : BlockRing n k₀ →+* ℂ :=
  eval₂Hom (Int.castRingHom ℂ) fun v ↦ w v.1 v.2

omit [Fintype ι] [DecidableEq ι] in
theorem evalBlock_apply {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (f : BlockRing n k₀) :
    evalBlock w f = evalCone w f := rfl

def atBlock (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    MvPolynomial (Coord n) ℤ →+* MvPolynomial (Coord n) ℂ :=
  (map (evalBlock w)).comp (sepBlock k₀).toRingHom

omit [Fintype ι] in
theorem atBlock_apply (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (q : MvPolynomial (Coord n) ℤ) :
    atBlock k₀ w q = map (evalBlock w) (sepBlock k₀ q) := rfl

def coeffVec (M : Finset (Coord n →₀ ℕ)) : MvPolynomial (Coord n) ℂ →ₗ[ℂ] (M → ℂ) :=
  LinearMap.pi fun μ ↦ lcoeff ℂ μ.1

omit [Fintype ι] [DecidableEq ι] in
theorem coeffVec_apply (M : Finset (Coord n →₀ ℕ)) (g : MvPolynomial (Coord n) ℂ) (μ : M) :
    coeffVec M g μ = coeff μ.1 g := rfl

end BlockSurjectivity

end

end GroundTheory.Heights₂.Heights
