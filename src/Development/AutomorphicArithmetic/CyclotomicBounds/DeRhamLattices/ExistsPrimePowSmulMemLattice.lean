import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticePowerSmul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.exists_pow_smul_mem_lattice_alt {l : ℕ} [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T :=
  _root_.UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt LL T v

theorem _root_.UpperTheory.KN.exists_prime_pow_smul_mem_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ (n : ℕ) (x : ↥T.L.T), (x : T.V) = ((l : ℚ_[l]) ^ n) • v := by
  intro l _ LL T v
  obtain ⟨n, hn⟩ := UpperTheory.KN.exists_pow_smul_mem_lattice_alt LL T v
  refine ⟨n, ⟨_, hn⟩, ?_⟩
  rw [← algebraMap_smul ↥LL.1 ((l : ℚ_[l]) ^ n) v, map_pow, map_natCast]
