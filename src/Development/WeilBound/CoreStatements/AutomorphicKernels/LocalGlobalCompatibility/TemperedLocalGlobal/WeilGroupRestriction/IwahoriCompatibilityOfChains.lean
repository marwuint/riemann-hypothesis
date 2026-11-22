import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import ReciprocityTheory.NeutralLocalFields.GrunwaldWang
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.NormVEqPowResF

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

structure CMExt (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] where
  M : Type
  [fld : Field M]
  [nf : NumberField M]
  [cm : IsCMField M]
  [alg : Algebra E M]
  [algO : Algebra M Ω]
  [tower : IsScalarTower E M Ω]
  [cl : IsAlgClosure M Ω]

attribute [instance] CMExt.fld CMExt.nf CMExt.cm CMExt.alg CMExt.algO CMExt.tower CMExt.cl

def CMExt.self (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] : CMExt E Ω :=
  { M := E }

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def SmoothSub {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (V : Subgroup (Weil h)) : Prop :=
  ∃ O : Subgroup (G E Ω), IsOpen (O : Set (G E Ω)) ∧ ∀ σ : Weil h, deg σ = 0 → (σ : G E Ω) ∈ O → σ ∈ V

inductive Chain {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : Subgroup (Weil h) → Prop
  | top : Chain h ⊤
  | step {U V : Subgroup (Weil h)} : Chain h U → V ≤ U → (V.subgroupOf U).Normal → (V.relIndex U).Prime → SmoothSub V → Chain h V

structure GoodSub (H : Subgroup (G E Ω)) : Prop where
  normal : H.Normal
  isOpen : IsOpen (H : Set (G E Ω))
  cyc : ∃ g : G E Ω, H ⊔ Subgroup.zpowers g = ⊤
  cm : ∀ L : IntermediateField E Ω, H ≤ L.fixingSubgroup → IsCMField L

end

section

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ}

structure IsLift (X : CMExt E Ω) (π : CuspSub E a) (P : CuspSub X.M a) : Prop where
  csd : P.IsCsd
  reg : (CG.mk P).IsRegAlg
  res : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT
    (r' : G X.M Ω →* GL (Fin a) (Qbar l)) wt' HT', IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    IsGalRepOf P (quadChar X.M ^ a) ι r' wt' HT' → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r (resG E g) * p⁻¹

end

def K1 : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Type) [Finite S]
    (v : S → HeightOneSpectrum (𝓞 F)) (A : S → ValuationSubring Ω), Function.Injective v → (∀ s, IsPlaceOver (A s) (v s)) →
    ∀ χ : ∀ s, Dec (F := F) (A s) →* ℂˣ, (∀ s, IsOpen ((χ s).ker : Set (Dec (F := F) (A s)))) →
    ∃ ψ : G F Ω →* ℂˣ, IsOpen (ψ.ker : Set (G F Ω)) ∧ (∀ s (g : Dec (F := F) (A s)), ψ g = χ s g) ∧
      ∀ u : InfinitePlace F, u.IsReal → ∀ c : G F Ω, Neutral.GrunwaldWang.IsComplexConjugationAt u c → ψ c = 1

def OneStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg → ∀ X : CMExt E Ω, IsGalois E X.M → (Module.finrank E X.M).Prime →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
      (∃ g, g ∉ (resG E (E' := X.M) (Ω := Ω)).range ∧ (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0) →
      ∃ P : CuspSub X.M a, IsLift Ω X π P

def Main : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc →
      ∀ U : Subgroup (Weil h), Chain h U → (∀ t ∈ U, deg t = 0 → (rc (algNorm σ)).charPol t = (X - 1) ^ a) →
        ∃ (X : CMExt E Ω) (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w'), (resW h h').range = U ∧
          WD.res h h' (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) = WD.res h h' (rc (algNorm σ))

end PositivityTheory.Pf1.CLGD.K

end
