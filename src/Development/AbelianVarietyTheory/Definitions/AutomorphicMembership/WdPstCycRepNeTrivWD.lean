import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.Test

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) (LL : FinExt l)

section Generic

variable {LL} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))

theorem apply_eq_of_nilpotent {W : Type} [AddCommGroup W] [Module ℂ W] (hd : finrank ℂ W = 1) {v : W}
    (hv : v ≠ 0) (u : End ℂ W) (hu : IsNilpotent (u - 1)) : u v = v := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd ((u - 1) v)
  have hp : ∀ n : ℕ, ((u - 1) ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have hc0 : c = 0 := by
    have := hp k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact pow_eq_zero_iff'.mp (this.resolve_right hv) |>.1
  rw [hc0, zero_smul, LinearMap.sub_apply, eq_comm, sub_eq_zero] at hc
  exact hc

end Generic

theorem lpDim_wdAt {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) :
    (wdAt P ι Bw h hj r).lpDim = a := by
  by_cases hr : IsPstAt P Bw r
  · obtain ⟨LL', r', -, h2, h3⟩ := wdAt_of_isPstAt ι Bw h hj hr
    rw [h3, lpDim_wdPst ι Bw h hj h2, LetterDim.finrank_wdSpace l P ι _ LL' _ _ h2]
    simp
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, lpDim_trivWD]

omit P ι in

theorem exists_induces (hw : w ∈ placesOver E l) (h : IsPlaceOver A w) :
    ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), Induces Bw := by
  obtain ⟨j, L0, hj, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw h
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  exact ⟨L0, Bw, fun x => by rw [hB]; exact hj x⟩

end GlobalTheory.Pst.Test
