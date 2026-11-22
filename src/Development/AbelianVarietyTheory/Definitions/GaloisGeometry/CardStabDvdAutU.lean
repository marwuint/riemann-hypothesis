import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SpKerColToEqColCpl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (Λ : LevFam X.E X.K (R.N R.m) Pr.vGs) (Θ : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def frmMem : MemOn (chF W sel mu L u R.m) where
  G := FrmG Λ Θ
  D := ChPt (R := R) sel mu u R.m
  actD := frmAct Λ Θ
  ρ := frmRho (colValF W sel mu u R.m) Λ Θ
  Nab := (colValF W sel mu u R.m).Nab
  Del := (colValF W sel mu u R.m).Del

@[reducible] def cplMem : MemOn (chF W sel mu L u (m2 + 1)) :=
  MemOn.pairs (chF W sel mu L u (m2 + 1)) b (ybCpl W sel mu cst L u m2 b hY)

@[reducible] def levFam : ℕ → GFam X.K :=
  spFam (chF W sel mu L u) m2 R.m (cplMem W sel mu cst L u m2 b hY) (frmMem W sel mu L u Λ Θ)

variable {W sel mu cst L u m2 b hY Λ Θ}

def levPt : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).D β → ChPt (R := R) sel mu u i
  | _, .mat _ _ => fun p => p
  | _, .cpl rfl => fun p => p.1.1
  | _, .top rfl => fun p => p

def levQ : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevQFam X.E X.K (R.N i) (QE sel (mu : Chr X.F X.E X.K))
  | i, .mat al _ => L.levQ i al
  | _, .cpl rfl => L.levQ (m2 + 1) b
  | _, .top rfl => Θ

end Fam

end GlobalTheory.GO
