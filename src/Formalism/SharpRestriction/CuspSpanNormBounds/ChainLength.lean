import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate

open scoped Classical in

def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      M.Ns s t t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * M.N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = M.Ns s t t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * M.N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, M.N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * M.N0 (h a) (h b) -
      Th x a b).PosSemidef)

def SelfDualLatticeNormCongruenceAt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (abelian₂ : Submodule M.L.O V), H.IsSelfDual abelian₂ →
  ∀ (T T' : F), (∃ u v : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) = T ∧ ((v : 𝒪[F]) : F) = T') →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E), IsUnit Zh.det →
    Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det *
        M.L.cj (Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det) ≠ 0 →
    ((∃ t : Term V M r, t.abelian₂ = abelian₂ ∧ t.T = T ∧ t.T' = T' ∧ H.IsTerm t ∧ H.Zhat t.f t.f' = Zh) ↔
      ∀ a b, HermSp.ZZplusOf M Zh T T' a b ∈ M.R)

def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
