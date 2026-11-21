import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DGamAut

open NumberField IsDedekindDomain Module Matrix MvPolynomial
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

structure LevCh (X : Fields) (Pr : Primes X) (R : Ranks) where
  β : ℕ → Type
  [finβ : ∀ j, Fintype (β j)]
  [decβ : ∀ j, DecidableEq (β j)]
  lev : ∀ j, β j → LevFam X.E X.K (R.N j) Pr.vGs

attribute [instance] LevCh.finβ LevCh.decβ

def LevCh.one {X : Fields} {Pr : Primes X} {R : Ranks} (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) : LevCh X Pr R where
  β _ := Unit
  lev j _ := Λ j

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

@[reducible] def stepF (u : Pr.Word) (j : ℕ) : GFam X.K where
  β := Λ.β j
  V := (colVal W u j (Pr.vT u) Pr.vGs).V
  ιV := VVIdx (colVal W u j (Pr.vT u) Pr.vGs).lam
  bV := (colVal W u j (Pr.vT u) Pr.vGs).bV
  pair := (colVal W u j (Pr.vT u) Pr.vGs).pair
  G b := FormG (Λ.lev j b)
  D _ := DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs
  actD b := formAct (Λ.lev j b)
  ρ b := formRho (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j b)
  Nab _ := (colVal W u j (Pr.vT u) Pr.vGs).Nab
  Del _ := (colVal W u j (Pr.vT u) Pr.vGs).Del

theorem stepF_mem (u : Pr.Word) (j : ℕ) (b : Λ.β j) :
    (stepF W Λ u j).mem b = formGSD (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j b) := rfl

theorem stepFOk (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (stepF W Λ u j).Ok :=
  fun _ => formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)

abbrev StClC (u : Pr.Word) (j : ℕ) : Type := (stepF W Λ u j).Cl

variable {W Λ} in

def repC {u : Pr.Word} {j : ℕ} (c : StClC W Λ u j) : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs :=
  ((stepF W Λ u j).mem c.1).outSec.rep c.2

@[irreducible] def recDGamAllC (Λ : LevCh X Pr R) {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : ℕ := dGamAut X R

theorem recDGamAllC_eq {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : recDGamAllC W Λ hX G = dGamAut X R := by
  unfold recDGamAllC
  rfl

theorem recDGamAllC_pos {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) : 0 < recDGamAllC W Λ hX G := by
  rw [recDGamAllC_eq]
  exact dGamAut_pos hX

theorem recDGamAllC_dvd {σ₀ : X.K →+* ℂ} (hX : X.Ok) (G : ChainGlob W σ₀) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m)
    (c : StClC W Λ u j) : Nat.card (FamStab (stepF W Λ u j) c) ∣ recDGamAllC W Λ hX G := by
  rw [recDGamAllC_eq]
  exact formGSD_stab_dvd_dGamAut hX (dga_N_mono R hj) (colVal W u j (Pr.vT u) Pr.vGs) (Λ.lev j c.1) (repC c)

end Step

section RhoPt

variable {X : Fields} {Pr : Primes X} {R : Ranks}

open Classical in

def rhoPt (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N i) := ⟨(R.N_pos i).ne'⟩
    (Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^
        (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  else 1

open Classical in

def rhoPt' (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N (i + 1)) := ⟨(R.N_pos (i + 1)).ne'⟩
    Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
              (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi
        (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^ (((R.N i / 2 : ℕ) : ℤ))
  else 1

theorem rhoPt_norm {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) {u : Pr.Word} (i : ℕ)
    (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) : ‖σ₀ (rhoPt G.chr i p : X.K)‖ = 1 := by
  unfold rhoPt
  split_ifs with hc
  · exact (rec_norm_units σ₀ (rec_norm_detTw σ₀ (G.chr.muAt_unit G.chr_unit i) _ _) (rec_norm_detTw σ₀ G.chr_unit.2 _ _) _).1
  · simp

theorem rhoPt'_norm {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) {u : Pr.Word} (i : ℕ)
    (p : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) : ‖σ₀ (rhoPt' G.chr i p : X.K)‖ = 1 := by
  unfold rhoPt'
  split_ifs with hc
  · exact (rec_norm_units σ₀ (rec_norm_detTw σ₀ (G.chr.muAt_unit G.chr_unit i) _ _) (rec_norm_detTw σ₀ G.chr_unit.2 _ _) _).2
  · simp

end RhoPt

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

structure ChainArgC {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (u : Pr.Word) where
  kk : ∀ i, GFam.Mat (stepF W Λ u i) (stepF W Λ u (i + 1))
  unf : ∀ i, StClC W Λ u i → StClC W Λ u (i + 1) → ((FrS X σ₀ (R.N i) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N (i + 1)) → ℂ))
  unf_ev : ∀ i (c : StClC W Λ u i) (c' : StClC W Λ u (i + 1)) (x : VV X.K (W.lamTrue u i)),
    mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
        (unf i c c' (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) (evV X.emb 1 (W.lamTrue u i) σ₀ x))) =
      (σ₀ (rhoPt G.chr i (repC c) : X.K) * σ₀ (rhoPt' G.chr i (repC c') : X.K))⁻¹ •
        evV X.emb 1 (W.lamTrue u (i + 1)) σ₀ ((kk i c.1 c'.1).k (repC c) (repC c') x)

variable {W Λ}

def ChainArgC.toF {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {u : Pr.Word} (A : ChainArgC W Λ G u) : ChainArgF R (stepF W Λ u) σ₀ where
  rhoDet i c := σ₀ (rhoPt G.chr i (repC c) : X.K)
  rhoDet' i c := σ₀ (rhoPt' G.chr i (repC c) : X.K)
  rho_norm i _ c := rhoPt_norm G i (repC c)
  rho'_norm i _ c := rhoPt'_norm G i (repC c)
  unf := A.unf

def recChainC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (A : ChainArgC W Λ G u) : ColumnChain R X.Tau (W.hc u) :=
  recChainF (W.hc u) (stepF W Λ u) (stepFOk W Λ hX u) σ₀ (recDGamAllC W Λ hX G) (recDGamAllC_pos W Λ hX G)
    (fun j hj c => recDGamAllC_dvd W Λ hX G u j hj c) A.toF

end Chain

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFamC (Λ : LevCh X Pr R) (u : Pr.Word) : Type :=
  ∀ i, Λ.β i → Λ.β (i + 1) → DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs → DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs →
    HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFamC Λ u)

variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
