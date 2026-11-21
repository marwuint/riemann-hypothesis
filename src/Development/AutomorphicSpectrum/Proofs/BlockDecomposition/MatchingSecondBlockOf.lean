import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMPlaces

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcN.F2 (mconv phi3 gconv leviOf IsHk)
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_mul_mul {a b : ℕ} {w : Pl E} (r s : ℂ) (u v : GLw a w × GLw b w → ℂ) :
    mconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * mconv u v y := by
  funext y
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem lconv_mul_mul {w : Pl E} (r s : ℂ) (u v : UL n w → ℂ) :
    lconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * lconv u v y := by
  funext y
  unfold lconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

section T

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

abbrev cc (d : LocData E n) (w : Pl E) : ↥(d.c w).support → ℂ := fun j => d.c w j.1

abbrev xx (d : LocData E n) (w : Pl E) : ↥(d.c w).support → Fin n → ℤ := fun j => j.1

theorem qT_eq (s : Finset (Fin (n / 2))) :
    d.qT a w s = fun y => (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
      MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s y := by
  funext y
  unfold LocData.qT MT.entT
  by_cases h : LocData.admitted n a s
  · have h' : MT.admitted n a s := ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
    rw [dif_pos h, dif_pos h', Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Tail.dc2
    ring
  · have h' : ¬ MT.admitted n a s := fun h' => h ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2.1, h'.2.2.2.2⟩
    rw [dif_neg h, dif_neg h', mul_zero]

theorem mpow_scale {b : ℕ} (r : ℂ) (u : GLw a w × GLw b w → ℂ) (k : ℕ) :
    MT.mpow w (fun y => r * u y) k = fun y => r ^ k * MT.mpow w u k y := by
  induction k with
  | zero =>
    funext y
    simp [MT.mpow]
  | succ k ih =>
    show mconv _ (MT.mpow w _ k) = _
    rw [ih, mconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * mconv u (MT.mpow w u k) y
    ring

theorem lpow_scale (K : Subgroup (UL n w)) (r : ℂ) (g : UL n w → ℂ) (k : ℕ) :
    lpow K (fun y => r * g y) k = fun y => r ^ k * lpow K g k y := by
  induction k with
  | zero =>
    funext y
    simp [U.lpow]
  | succ k ih =>
    show lconv _ (lpow K _ k) = _
    rw [ih, lconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * lconv g (lpow K g k) y
    ring

theorem unitary_function_at_T (hT : w ∈ d.T) : d.g₀ w = fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
    ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) y := by
  have h : d.g₀ w = fun y => (d.c w).sum fun x t =>
      t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y := by
    unfold LocData.g₀
    rw [if_pos hT]
  rw [h]
  funext y
  rw [Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end T

end GlobalTheory.CompanionTheory.MatchLMPlaces

end
