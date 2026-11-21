import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

structure IsAdapted (C : GL (Fin n) E) : Prop where
  le : 2 * r ≤ n
  colX : ∀ (i : Fin n) (j : Fin r), i.val = j.val → ∀ k, C.1 k i = X k j
  columnBlock : ∀ (i : Fin n) (j : Fin r), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j
  perpX : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) X * J) *ᵥ (fun k => C.1 k i) = 0
  perpY : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i) = 0

def blkCols {l d : ℕ} (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin d) E :=
  Z.submatrix id fun j => ⟨l + j.val, by omega⟩

def IsBlockEmb {l d : ℕ} (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J) : Prop :=
  ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
    Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
    (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) ∧
    ∀ g : GlobalTheory.CuspRep.GA E d, (matHom _ σ J (ι g)).1 =
      1 + adMat F (blkCols h X) * (g.1.map Φ.symm - 1) * adMat F (cT (σ : E →+* E) (blkCols h Y) * J) +
        adMat F (blkCols h Y) * (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm) - 1) *
          adMat F (cT (σ : E →+* E) (blkCols h X) * J)

end GlobalTheory.BlockForms

end
