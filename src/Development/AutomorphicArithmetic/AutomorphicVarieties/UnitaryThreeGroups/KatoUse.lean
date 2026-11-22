import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg

namespace UpperTheory.V.U3

def KatoUse : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ (f : Af.Newform (2 * e + 1)) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
      f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → Af.KillsMu M φ →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W φ))

structure CohInp : Prop where
  loc : Loc.LocalPublishedTheorems
  pt : GlobalTheory.Published.PoitouTateNormalised
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  lemK : ∃ CK : ℝ, LemmaK CK

structure Inp : Prop extends CohInp where
  lemM : LemmaM
  lemM' : LemmaM'
  lemP : LemmaP
  kato : KatoUse
  adK : Af.AdVanishK
  adQ : Af.AdVanishQ
  newAut : Af.NewformAut
  number : Af.CongruenceNumberRankThree

def PropGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p : ℕ), 1 ≤ e → p.Prime → ¬ p ∣ 30 * N * (discr K).natAbs →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c₅ * Nat.totient H.index * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] (l : ℕ) [Fact l.Prime], l ≠ p →
        ∀ c : Coef l, (∃ ψ ∈ orb c H, GD Ω K l e ψ) →
          (∀ ψ ∈ orb c H, Vlen Ω c e ψ ≠ ⊤) ∧ ∑ ψ ∈ orb c H, Vn Ω c e ψ ≤ 2 * (padicValInt l NN : ℝ)

def CorGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p p' : ℕ), p.Prime → p'.Prime → p ≠ p' →
    ¬ p ∣ 30 * N * (discr K).natAbs → ¬ p' ∣ 30 * N * (discr K).natAbs →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, ∃ ψ ∈ orb (c l) H, GD Ω K l e ψ) →
      (∀ l ∈ Ls, ∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤
        2 * c₅ * (Nat.totient H.index) * ((N : ℝ) * (e + 1)) ^ A * (Real.log p + Real.log p')

end UpperTheory.V.U3

end
