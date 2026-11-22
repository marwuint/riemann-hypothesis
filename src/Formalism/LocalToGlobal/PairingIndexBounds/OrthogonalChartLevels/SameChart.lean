import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtRec
import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.G.Cmp
open Formalism.L2.Col Formalism.HermitianLatticesTheory
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def LamPos : Prop :=
  ∀ (τ : D.what₂.Tau) (x : D.host.E) (hx : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar),
    lam ⟨TaylorLogMetric.embT D τ x, hx⟩ =
      twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2
        ((I.eQ ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1).symm
          (fstV I ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 (inclE (F := D.host.F) (((I.plc ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1)).adicCompletion D.host.F)
            (if IsOddPos ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2 then D.host.conj x else x))))

end Formalism.L2.PairingIndexBounds.F
