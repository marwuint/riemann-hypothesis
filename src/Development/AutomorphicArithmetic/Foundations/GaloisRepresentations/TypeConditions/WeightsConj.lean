import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Transported

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalN (Ab)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def TmW (y : WD h) : Prop :=
  ∀ σ : G E Ω, (∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1) → y.inePol σ = (X - 1) ^ y.lpDim

def SqW (y : WD h) : Prop :=
  ∀ γ ∈ Ine (F := E) A, ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ {σ : G E Ω | ∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1}) : Subgroup (G E Ω)) :
        Set (G E Ω)) →
    ∀ z : ℂ, thr w y.lpDim ≤ (y.inePol γ).rootMultiplicity z → z ^ (normV w - 1) = 1

def NcW (y : WD h) : Prop := TmW y ∧ y.mono0 ∧ SqW y

structure Aw (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim
  unr : y.unr → x = y
  ine : NcW y → ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g
  mono : NcW y → x.mono0

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

def Nice (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ ∃ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc ∧ NcW (rc (algNorm σ))

structure AboveU (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  deRham : Nice π h → IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)
  jumps : Nice π h → ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure IsGalU (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → Aw (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveU π ι r HT P h Bw hj

theorem IsGalU.aw {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : IsGalU π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    Aw (wdOf h hl ι r) ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2)) :=
  rec_algNorm hrc σ ▸ H.away w hl A h rc hrc σ hσ

end UpperTheory.GalS
