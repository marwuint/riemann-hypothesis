import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section General

variable {O Γ : Type} [CommRing O] [IsDomain O] [Group Γ]

def fracRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) :
    Representation (FractionRing O) Γ (Fin a → FractionRing O) :=
  glRep (mapRep (algebraMap O (FractionRing O)) ρ)

def charSum (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ (Fin t → FractionRing O) where
  toFun g := LinearMap.pi fun c : Fin t =>
    algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) • LinearMap.proj c
  map_one' := by
    ext v c
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext c
    simp [mul_assoc, Algebra.smul_def]

def blockRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ ((Fin a → FractionRing O) × (Fin t → FractionRing O)) :=
  (fracRep ρ).prod (charSum χ t)

def IsoBlock {n a : ℕ} (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ))
    (t : ℕ) : Prop :=
  ∃ e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin a → FractionRing O) × (Fin t → FractionRing O)),
    ∀ g v, e (fracRep r g v) = blockRep ρ χ t g (e v)

def BlockSemisimple {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) : Prop :=
  (blockRep ρ χ t).IsSemisimpleRepresentation

omit [IsDomain O] in

def LatticeContinuous [TopologicalSpace Γ] [TopologicalSpace O] {a : ℕ}
    (ρ : Γ →* GL (Fin a) O) : Prop :=
  Continuous fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)

theorem blockRep_apply {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : (Fin a → FractionRing O) × (Fin t → FractionRing O)) :
    blockRep ρ χ t g v =
      ((((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map
          (algebraMap O (FractionRing O))).mulVec v.1,
        fun c : Fin t => algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) * v.2 c) := by
  rfl

end General

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

structure IsComplement (r₀ : G H.E N.Om →* GL (Fin R.nV) (N.O i))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop where

  rho : IsoBlock r₀ ρ (N.chi i) R.t

  ss : BlockSemisimple ρ (N.chi i) R.t

  cont : LatticeContinuous ρ

end Record

def Complement_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i,
    ∀ r₀ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i), IsHeckeGalois D.nd i π r₀ →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsComplement D.nd i r₀ ρ

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

end
