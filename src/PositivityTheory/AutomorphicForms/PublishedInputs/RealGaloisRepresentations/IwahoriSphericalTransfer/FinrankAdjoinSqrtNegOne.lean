import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.RealGal

structure QCM (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] where

  K : IntermediateField F Ω
  nf : NumberField ↥K
  cm : @IsCMField ↥K _ nf.to_charZero
  two : Module.finrank F ↥K = 2

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

instance (Q : QCM F Ω) : NumberField ↥Q.K := Q.nf

instance (Q : QCM F Ω) : IsCMField ↥Q.K := Q.cm

instance [IsAlgClosure F Ω] (Q : QCM F Ω) : IsAlgClosure ↥Q.K Ω :=
  ⟨IsAlgClosure.isAlgClosed F, haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩

section Gauss

open Polynomial
open scoped IntermediateField

theorem QCM.sq_ne_neg_one_of_isReal {E : Type} [Field E] {v : InfinitePlace E} (hv : v.IsReal) (x : E) : x ^ 2 ≠ -1 := fun h => by
  have := congrArg (InfinitePlace.embedding_of_isReal hv) h
  rw [map_pow, map_neg, map_one] at this
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

omit [NumberField F] in

theorem QCM.isIntegral_sqrt_neg_one {i : Ω} (hi : i ^ 2 = -1) : IsIntegral F i :=
  ⟨X ^ 2 - C (-1), monic_X_pow_sub_C _ two_ne_zero, by simp [hi]⟩

theorem QCM.finrank_adjoin_sqrt_neg_one [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : Module.finrank F F⟮i⟯ = 2 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hirr : Irreducible (X ^ 2 - C (-1) : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (QCM.sq_ne_neg_one_of_isReal (IsTotallyReal.isReal v))
  rw [IntermediateField.adjoin.finrank (QCM.isIntegral_sqrt_neg_one hi),
    ← minpoly.eq_of_irreducible_of_monic hirr (by simp [hi]) (monic_X_pow_sub_C _ two_ne_zero), natDegree_X_pow_sub_C]

def QCM.gauss [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : QCM F Ω :=
  haveI := IntermediateField.adjoin.finiteDimensional (QCM.isIntegral_sqrt_neg_one (F := F) hi)
  haveI nf : NumberField F⟮i⟯ := NumberField.of_module_finite F _
  haveI : IsTotallyComplex F⟮i⟯ := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    exact fun hv => QCM.sq_ne_neg_one_of_isReal hv (IntermediateField.AdjoinSimple.gen F i) (Subtype.ext (by simpa using hi))⟩
  haveI : Algebra.IsQuadraticExtension F F⟮i⟯ := { finrank_eq_two' := QCM.finrank_adjoin_sqrt_neg_one hi }
  { K := F⟮i⟯
    nf := nf
    cm := IsCMField.ofCMExtension F _
    two := QCM.finrank_adjoin_sqrt_neg_one hi }

theorem QCM.gauss_K [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : (QCM.gauss (F := F) hi).K = F⟮i⟯ := rfl

theorem QCM.nonempty [IsTotallyReal F] [IsAlgClosure F Ω] : Nonempty (QCM F Ω) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) two_pos
  exact ⟨QCM.gauss hi⟩

end Gauss

def AttRes [IsTotallyReal F] {l : ℕ} [Fact l.Prime] {a : ℕ} (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω] (r : G L Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, π.HasSat (w.under (𝓞 F)) B ∧ FrobEig ι r w ((algSat a (normV (w.under (𝓞 F))) B).map (· ^ f))

section Att

variable {L : Type} [Field L] [NumberField L] [Algebra F L]

theorem AttRes.normV_eq_pow (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F)
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

end Att

end GlobalTheory.RealGal

end
