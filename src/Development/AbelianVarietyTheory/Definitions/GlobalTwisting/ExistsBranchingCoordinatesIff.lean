import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word}

structure Pend (X : Ch D u) where

  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)

  coM : D.what₂.places.Pl → X.fm.clsP → ((X.C.Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)

  coP : D.what₂.places.Pl → (X.P.Wrow →ₗ[ℂ] (X.fm.clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

  coM_mem : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) ∈ CSpan (X.fm.lam D.R.m)

  coM_inj : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) = 0 → φ (X.fm.til c) = 0

  coP_mem : ∀ w, ∀ z ∈ X.fm.ptC, ∀ c, coP w z c ∈ CSpan X.fm.sg

  coP_inj : ∀ w, ∀ z ∈ X.fm.ptC, coP w z = 0 → z = 0

  Pt_eq : ∀ w, ∀ φ ∈ X.fm.Fi D.R.m, ∀ c,
    coP w (Pt X φ) c = blk (fun τ => br τ) (coM w c (φ (X.fm.til c)))

  lat_co : ∀ w, ∀ x ∈ X.fm.S D.R.m w, ∀ c,
    coM w c (X.fm.emb D.R.m x (X.fm.til c)) ∈ IntSpan D w (X.fm.lam D.R.m)

  pt_co : ∀ w, ∀ z ∈ X.fm.ptC, (∃ y ∈ X.fm.SP w, X.fm.ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w X.fm.sg

  gP : D.what₂.places.Pl → X.fm.clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ

  ipV_co : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, (X.fm.ipV D.R.m (X.fm.til c) (φ (X.fm.til c)) (φ (X.fm.til c))).re =
    (nfAll (X.fm.lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))).re

  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ X.fm.ptC, (X.fm.ipP z z).re = ∑ c, ((Nat.card (X.fm.stabilizer₂ c) : ℝ))⁻¹ *
    (nfAll X.fm.sg (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))).re

  beOn_eq : ∀ τ, X.fm.beOn τ = opNorm X τ (br τ)

  interlace : X.fm.SgInterlace

variable {X : Ch D u}

def ArchimedeanSignatureMatching (P : Pend X) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr X τ) (sgTr X τ) (P.br τ)

def Pend.ofRecord (P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u) : Pend (own D u) :=
  ⟨P.br, P.coM, P.coP, P.coM_mem, P.coM_inj, P.coP_mem, P.coP_inj, P.Pt_eq, P.lat_co, P.pt_co, P.gP, P.ipV_co,
    P.re_petersson_self_eq_sum_coord, P.beOn_eq, P.interlace⟩

def Pend.toRecord (P : Pend (own D u)) : Formalism.MainNotions.product_first_zeroth_parts.Pend D u :=
  ⟨P.br, P.coM, P.coP, P.coM_mem, P.coM_inj, P.coP_mem, P.coP_inj, P.Pt_eq, P.lat_co, P.pt_co, P.gP, P.ipV_co,
    P.re_petersson_self_eq_sum_coord, P.beOn_eq, P.interlace⟩

theorem branchingLaw_ofRecord_iff (P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u) : ArchimedeanSignatureMatching (Pend.ofRecord P) ↔ Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P := Iff.rfl

theorem branchingCoordinates_iff (P : Pend (own D u)) : Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P.toRecord ↔ ArchimedeanSignatureMatching P := Iff.rfl

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f =
    ((∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hc, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem fockF_self_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.REAL.fockF f f).re := by
  rw [fockF_self_eq, Complex.ofReal_re]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  refine Finset.sum_pos (fun n hn => ?_) ⟨m, MvPolynomial.mem_support_iff.mpr hm⟩
  have h1 : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have h2 : 0 < Complex.normSq (f.coeff n) := Complex.normSq_pos.mpr h1
  have h3 : (0 : ℝ) < ((∏ k ∈ n.support, (n k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun k _ => Nat.factorial_pos _)
  exact mul_pos h2 h3

end GlobalTheory.LvT
