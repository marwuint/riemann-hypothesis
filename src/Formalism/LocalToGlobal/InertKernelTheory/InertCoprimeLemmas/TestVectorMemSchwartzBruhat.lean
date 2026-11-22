import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.ThirdClauseIntegralCombination
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

variable {δ}

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

def intR (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem constantCoeff_lift {σ : Type*} (G : MvPowerSeries σ (intR p)) :
    ((MvPowerSeries.constantCoeff G : intR p) : ℂ_[p]) =
      MvPowerSeries.constantCoeff (MvPowerSeries.map (intR p).subtype G) := by
  rfl

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

def dl (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) :
    MvPowerSeries (Fin r) ℂ_[p] →+ MvPowerSeries (Fin r) ℂ_[p] where
  toFun G := algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) c *
    PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w * MvPowerSeries.pderiv ℂ_[p] j G
  map_zero' := by simp
  map_add' F G := by simp only [map_add]; ring

theorem dl_apply (c : ℂ_[p]) (w : PowerSeries ℂ_[p]) (j : Fin r) (G : MvPowerSeries (Fin r) ℂ_[p]) :
    dl c w j G = algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) c *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) w * MvPowerSeries.pderiv ℂ_[p] j G := rfl

end Deriv

section Chain

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Chain

section Lin

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Lin

end JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

end Formalism.L2.KerInert
