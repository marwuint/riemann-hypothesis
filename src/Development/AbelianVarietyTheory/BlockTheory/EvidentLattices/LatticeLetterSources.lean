import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeLetterSources

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

abbrev FinalTheorems (o : LamObj c nΨ n') : Type := (Fin o.xΨ.P.g × Fin nΨ) ⊕ (Fin o.x'.P.g × Fin n')

def FinalTheorems.chr {o : LamObj c nΨ n'} : FinalTheorems o → (E →+* ℂ)
  | .inl s => (o.τΨ s.1).1
  | .inr s => (o.τ' s.1).1

def FinalTheorems.copy {o : LamObj c nΨ n'} : FinalTheorems o → ℕ
  | .inl s => s.2
  | .inr s => s.2

def FinalTheorems.line {o : LamObj c nΨ n'} : FinalTheorems o → MLine o.K₁
  | .inl s => o.ℓΨ s.1
  | .inr s => o.ℓ' s.1

def FinalTheorems.img {o : LamObj c nΨ n'} : FinalTheorems o → (Sp (DualNumber o.K₁) ⟶ o.B.A.left)
  | .inl s => (o.xΨ.v s.1).left ≫ o.φΨg ≫ (o.φΨ s.2).left
  | .inr s => (o.x'.v s.1).left ≫ o.φ'g ≫ (o.φ' s.2).left

structure LamLetters (o : LamObj c nΨ n') : Type where
  m : (E →+* ℂ) → ℕ
  e : (Σ τ : E →+* ℂ, Fin (m τ)) ≃ Fin o.xB.P.g
  src : Fin o.xB.P.g → FinalTheorems o
  U : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁
  ℓ : Fin o.xB.P.g → MLine o.K₁

variable {o : LamObj c nΨ n'}

def LamLetters.IsLetter (L : LamLetters o) (k : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A) : Prop :=
  w.left ≫ o.φB = (L.src k).img

def LamLetters.IsEvident (L : LamLetters o) : Prop :=
  Function.Bijective L.src ∧
  (∀ (τ : E →+* ℂ) (i : Fin (L.m τ)), (L.src (L.e ⟨τ, i⟩)).chr = τ ∧ (L.src (L.e ⟨τ, i⟩)).copy = (i : ℕ)) ∧
  ∀ k, L.ℓ k = (L.src k).line

def LamLetters.IsGood (L : LamLetters o) : Prop :=
  L.IsEvident ∧ ∀ k, ∃ w : epsR o.K₁ ⟶ o.xB.P.A, L.IsLetter k w ∧ IsLieComb (L.U k) o.xB.v w

end Letters

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def frameOf {r : ℕ} (Xx : DataX E r) {X : Data E r} (hX : Xx.toData = X) (x : Frame X.Ψ r) : Frame Xx.Ψ r :=
  cast (congrArg (fun Y : Data E r => Frame Y.Ψ r) hX.symm) x

theorem frameOf_rfl {r : ℕ} (Xx : DataX E r) (x : Frame Xx.Ψ r) : frameOf Xx rfl x = x := rfl

end Point

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeLetterSources
