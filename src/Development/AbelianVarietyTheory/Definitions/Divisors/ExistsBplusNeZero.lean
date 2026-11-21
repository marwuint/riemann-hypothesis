import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.FunObjModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isMeasLevW_unique {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {good} {μ μ' : Measure (GA D V)}
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) (h : Lev.IsMeasLevW V K good μ) (h' : Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hall⟩ := h
  obtain ⟨hμ', -, hall'⟩ := h'
  obtain ⟨⟨A, hA⟩, hallA⟩ := hall θ hθ
  obtain ⟨⟨m, hm⟩, hallm⟩ := hallA A hA
  have hvol := hallm m hm
  have hvol' := (hall' θ hθ).2 A hA |>.2 m hm

  choose C hC hC1 using fun ρ => exists_compact_mem_nhds (1 : Formalism.BasicNotions.UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
  have hB : ∀ ρ, MeasurableSet (interior (C ρ)) := fun ρ => isOpen_interior.measurableSet
  have hpos : ∀ ρ, m ρ (interior (C ρ)) ≠ 0 := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact isOpen_interior.measure_ne_zero (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 (hC1 ρ)⟩
  have hfin : ∀ ρ, m ρ (interior (C ρ)) ≠ ⊤ := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact ((measure_mono interior_subset).trans_lt (hC ρ).measure_lt_top).ne
  have e1 := hvol (fun ρ => interior (C ρ)) hB
  have e2 := hvol' (fun ρ => interior (C ρ)) hB
  set P := ∏ ρ, m ρ (interior (C ρ)) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hpos ρ
  have hPtop : P ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hfin ρ
  have := hμ
  have := hμ'

  obtain ⟨c, hs⟩ : ∃ c : NNReal, μ' = c • μ := ⟨_, MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ' μ⟩
  have e3 : ∀ s, μ' s = c * μ s := fun s => by
    simp only [hs, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [e3, e1] at e2
  have hc1 : c = 1 := by exact_mod_cast (ENNReal.mul_eq_right hP0 hPtop).1 e2
  rw [hs, hc1, one_smul]

theorem isAt_unique {M M' : Vol G} {X : Node} {K} (h : M.IsAt X K) (h' : M'.IsAt X K) : M.ν X = M'.ν X := by
  unfold Vol.IsAt at h h'
  split_ifs at h h'
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1

variable (W : G.Weil)

theorem levJ_col (t : T) (j : ℕ) : levJ G t (.grid 0 (j + 1)) = levCol L t j := rfl

end GlobalTheory.FunObjModel

end
