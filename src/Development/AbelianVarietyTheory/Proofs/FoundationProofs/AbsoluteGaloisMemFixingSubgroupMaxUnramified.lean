import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective, IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
