import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousCharacter

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

def liftZ (p n : ℕ) (ε : 𝓞 D.host.K) {r : ℕ} (v : Fin r → VC D N N') : (Fin r → ℤ) →+ VC D N N' :=
  AddMonoidHom.mk' (fun z => (D.host.φ₀ ((ε : D.host.K) : D.host.E) / (p : ℂ) ^ n) • ∑ i, z i • v i) fun z z' => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

end GlobalTheory.MomT.FromComb
