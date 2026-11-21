import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil

namespace GlobalTheory.LeviBlockExponent

scoped instance valRelFv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ValuativeRel (Fv F v) :=
  GlobalTheory.LocalData.complRel v

scoped instance localFieldFv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def pairPlace {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) : (Σ j : Fin 2, Fin (b j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (by rw [Fin.sum_univ_two]; exact h))

def pairChar (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Levi k (fun j : Fin 2 => Fin (b j)) →* ℂˣ :=
  ∏ j, (detChar (Fin (b j)) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (Fin (b j)) k) j)

def pairInd {N : ℕ} (b : Fin 2 → ℕ) (h : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin N) k) (IndSp (pairPlace b h) (ofChar (pairChar k b χ))) :=
  parInd (pairPlace b h) (ofChar (pairChar k b χ))

end Local

end GlobalTheory.LeviBlockExponent
