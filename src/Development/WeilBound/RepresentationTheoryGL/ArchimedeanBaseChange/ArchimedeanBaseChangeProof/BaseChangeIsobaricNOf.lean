import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitS
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.LocalL
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.InertR
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcN

def CsdAsc {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ (a d : ℕ) (P : CuspSub E a), P.IsUnitary ∧ GlobalTheory.DiscSpec.IsNormalised P ∧ P.IsCsd ∧ PositivityTheory.Rg.Rs.AscEmb V P d

structure IsBaseChangeN {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ}
    {N : Fin c → ℕ} (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (m : Fin c → (E →+* ℂ) → Multiset ℂ)
    (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, CsdAsc (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  sub : ∀ w, GlobalTheory.SmGL.IsSubquotient (P w).ρ (locProd h w (σ · w))
  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (P w).ρ (GlobalTheory.LFun.KGL w n)
  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (P w).ρ (GlobalTheory.LGrp.bcParam n α)
  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (P w).ρ
  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

def BaseChangeIsobaricN : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ)
        (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))), IsBaseChangeN π h V σ m P

structure Datum (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, CsdAsc (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end PositivityTheory.Rg.BcN

end
