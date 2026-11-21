import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

abbrev algO (x : Sp S ⟶ X₀) (B : Type) [CommRing B] [Algebra S B] : Over X₀ :=
  Over.mk (spMap (algebraMap S B) ≫ x)

def algMap (x : Sp S ⟶ X₀) {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B']
    (f : B →ₐ[S] B') : algO x B' ⟶ algO x B :=
  Over.homMk (spMap (f : B →+* B')) (by
    change spMap (f : B →+* B') ≫ spMap (algebraMap S B) ≫ x = spMap (algebraMap S B') ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

def jetVec {σ : Type} (c : σ → S) : Jet S σ 1 →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S))
          (MvPolynomial.X i : MvPolynomial σ S)) ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

abbrev JetPts (G : Over X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Type :=
  ∀ m : ℕ, algO x (Jet S (Fin d) m) ⟶ G

section Group

variable (G : Over X₀) [GrpObj G] (x : Sp S ⟶ X₀) {d : ℕ}

def IsFormalParam (j : JetPts G x d) : Prop :=
  (∀ m, algMap x (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m) ∧
  (∀ m, algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1) ∧
  ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (I : Ideal B), I ^ (m + 1) = ⊥ →
    ∀ g : algO x B ⟶ G, algMap x (Ideal.Quotient.mkₐ S I) ≫ g = 1 →
      ∃! f : Jet S (Fin d) m →ₐ[S] B, algMap x f ≫ j m = g

omit [GrpObj G] in

def TanIs (j : JetPts G x d) (v : Sp (DualNumber S) ⟶ G.left) (c : Fin d → S) : Prop :=
  v = (algMap x (jetVec c) ≫ j 1).left

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem jetVec_X {σ : Type} (c : σ → S) (i : σ) :
    jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) = c i • (DualNumber.eps : DualNumber S) := by
  have h : jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      MvPolynomial.aeval (R := S) (fun i => c i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i) := rfl
  rw [h, MvPolynomial.aeval_X]

end GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
