import Formalism.LocalToGlobal.Columns.RecChainCUnfPol

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section XpL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λm : LevFam X.E X.K (R.N R.m) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def topGSD (u : Pr.Word) : GSD X.K := formGSD (colVal W u R.m (Pr.vT u) Pr.vGs) Λm

def topEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) : (topGSD W Λm u).Ev σ₀ :=
  roundEv σ₀ hσ (W.lamTrue u R.m) (fun d => d.1.Lsh) Λm

variable {W ΛM}

variable (ΛM) in

def LevExtL : Prop := ∀ h : ↥(ΛM.inv).grp, (extR R hSG ((1 : UF X.E (R.N R.m - 1)), h.1)).2 ∈ Λm.grp

variable {Λm}

variable (W Λm ΛM) in

def tilClL (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : (topGSD W Λm u).Cl :=
  (topGSD W Λm u).cls (tilR hSG u ((ptGSD W ΛM).outSec.rep c))

variable (W Λm ΛM) in

def lowCL (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  (topEv W Λm σ₀ hσ u).extend ((ptEv W ΛM σ₀ hσ).ev.comp (brC W u))

end XpL

section XpC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (bm : Λ.β R.m)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable {W Λ bm ΛM}

variable (W Λ bm ΛM) in

def tilClC (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : StClC W Λ u R.m := ⟨bm, tilClL W (Λ.lev R.m bm) hSG ΛM u c⟩

variable (W Λ bm ΛM) in

def lowCC (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  lowCL W (Λ.lev R.m bm) ΛM σ₀ hσ u

variable (W Λ bm) in

def resTop (σ₀ : X.K →+* ℂ) (u : Pr.Word) :
    (StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] ((topGSD W (Λ.lev R.m bm) u).Cl → FrS X σ₀ (R.N R.m) → ℂ) :=
  LinearMap.funLeft ℂ (FrS X σ₀ (R.N R.m) → ℂ) fun c₀ : (topGSD W (Λ.lev R.m bm) u).Cl => (⟨bm, c₀⟩ : StClC W Λ u R.m)

variable (bm) in

def recPerC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) : PeriodMap R (recChainC hX σ₀ G u A) where
  Mt := Fin ((rowGSD W ΛM).hDim hM) → ℂ
  Wz := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m) → ℂ
  evz := ((topEv W (Λ.lev R.m bm) σ₀ hσ u).evAt fun c => tilR hSG u ((ptGSD W ΛM).outSec.rep c)) ∘ₗ resTop W Λ bm σ₀ u
  Wrow := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => lowCC W Λ bm ΛM σ₀ hσ u ∘ₗ LinearMap.proj c
  period := periodC W ΛM hX σ₀ hσ hM

end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

end One

end Formalism.L2.Col
