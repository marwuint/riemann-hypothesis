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

theorem stepF_mem_top (u : Pr.Word) : (stepF W Λ u R.m).mem bm = topGSD W (Λ.lev R.m bm) u := rfl

def LevExtC : Prop := LevExtL (Λ.lev R.m bm) hSG ΛM

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

theorem resTop_apply (σ₀ : X.K →+* ℂ) (u : Pr.Word) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c₀ : (topGSD W (Λ.lev R.m bm) u).Cl) : resTop W Λ bm σ₀ u F c₀ = F ⟨bm, c₀⟩ := rfl

variable (bm) in

def recPerC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) : PeriodMap R (recChainC hX σ₀ G u A) where
  Mt := Fin ((rowGSD W ΛM).hDim hM) → ℂ
  Wz := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m) → ℂ
  evz := ((topEv W (Λ.lev R.m bm) σ₀ hσ u).evAt fun c => tilR hSG u ((ptGSD W ΛM).outSec.rep c)) ∘ₗ resTop W Λ bm σ₀ u
  Wrow := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => lowCC W Λ bm ΛM σ₀ hσ u ∘ₗ LinearMap.proj c
  period := periodC W ΛM hX σ₀ hσ hM

theorem recPerC_evz (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).evz F c =
      (topEv W (Λ.lev R.m bm) σ₀ hσ u).trPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) (F (tilClC W Λ bm hSG ΛM u c)) := rfl

end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem LevExtC_one : LevExtC (LevCh.one Λ₀) () hSG ΛM ↔ LevExt Λ₀ hSG ΛM := Iff.rfl

theorem tilClC_one (u : Pr.Word) (c : (ptGSD W ΛM).Cl) :
    tilClC W (LevCh.one Λ₀) () hSG ΛM u c = ⟨(), tilCl W Λ₀ hSG ΛM u c⟩ := rfl

theorem lowCC_one (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    lowCC W (LevCh.one Λ₀) () ΛM σ₀ hσ u = lowC W Λ₀ ΛM σ₀ hσ u := rfl

theorem recPerC_evz_one (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W (LevCh.one Λ₀) G u) (A₀ : ChainArg W Λ₀ G u) (hM : (rowGSD W ΛM).Ok)
    (F : StClC W (LevCh.one Λ₀) u R.m → FrS X σ₀ (R.N R.m) → ℂ) :
    (recPerC () hSG hX σ₀ hσ u G A hM).evz F = (recPer hSG hX σ₀ hσ u G A₀ hM).evz fun c₀ : StCl W Λ₀ u R.m => F ⟨(), c₀⟩ := rfl

end One

end Formalism.L2.Col
