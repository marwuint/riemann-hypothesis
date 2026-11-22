import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
import Formalism.LocalToGlobal.Columns.RowFormsRat
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.FormalDegreeBessel.FinalDS
import Mathlib.LinearAlgebra.Vandermonde

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

structure ColObj (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) where

  f : ℕ

  k : ℕ

  m : ℕ

  T : I → ℕ

  Mf : I → HLat K

  M : I → HLat K

  incl : ∀ u, (M u).V →ₗ[K] (Mf u).V

  Vr : ∀ u, InfinitePlace K → Matrix (Mf u).ι (M u).ι ℂ

  dstar : I → ℝ

  overPi : I → HeightOneSpectrum (𝓞 K) → Prop

  Nlam : ∀ u, HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (M u).V

  lamT : I → ℝ

  Nu : ∀ u, Submodule (𝓞 K) (M u).V

  supp : Finset (HeightOneSpectrum (𝓞 K))

  sg : I → HeightOneSpectrum (𝓞 K) → ℝ

  tau : HeightOneSpectrum (𝓞 K) → ℝ

  zLow : I → ℝ

  zUp : I → ℝ

  Dstar : ℝ

  Xu : I → ℝ

  xLow : ℝ

  xUp : ℝ

  xVar : ℝ

  Mtil : HLat K

namespace ColObj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I)

def S : Finset (Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) := C.supp.map (plEquiv K).toEmbedding

def sgExpW (u : I) (w : HeightOneSpectrum (𝓞 K)) : ℤ := ⌊(eW w : ℝ) * C.sg u w⌋

def sgExp (u : I) : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.indicator C.S fun z _ => C.sgExpW u ((plEquiv K).symm z)

def tauExpW (w : HeightOneSpectrum (𝓞 K)) : ℤ := ⌊(eW w : ℝ) * C.tau w⌋

def tauExp : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.indicator C.S fun z _ => C.tauExpW ((plEquiv K).symm z)

def ItM (u : I) : Submodule (𝓞 K) (C.M u).V :=
  Formalism.HermitianLatticesTheory.idealSmul ((Formalism.LFunctionChainParameters.slopeLatticeData.idealPow C.tauExp : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) (C.M u).L

def Npr (u : I) : Submodule (𝓞 K) (C.M u).V := Formalism.LFunctionChainParameters.slopeLatticeData.modLat (C.sgExp u) (C.Nu u)

def lenMN (u : I) (w : HeightOneSpectrum (𝓞 K)) : ℚ := lenUW w (C.M u).L (C.Nu u)

def dM (u : I) : ℕ := Fintype.card (C.Mf u).ι

end ColObj

structure ColIface (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) extends ColObj K I where

  cplx : IsTotallyComplex K
  f_pos : 0 < f

  T_prime : ∀ u, (T u).Prime

  T_big : ∀ u, 4 * f ≤ T u

  Mf_good : ∀ u, (Mf u).Good

  M_good : ∀ u, (M u).Good
  incl_inj : ∀ u, Function.Injective (incl u)

  incl_norm : ∀ u v (x : (M u).V),
    Formalism.HermitianLatticesTheory.normAt (M u).b (M u).X v x = Formalism.HermitianLatticesTheory.normAt (Mf u).b (Mf u).X v (incl u x)

  M_L : ∀ u, (M u).L = (Mf u).L.comap ((incl u).restrictScalars (𝓞 K))

  Vr_iso : ∀ u v, (Vr u v)ᴴ * Vr u v = 1

  Vr_fcoord : ∀ u v (x : (M u).V),
    Formalism.HermitianLatticesTheory.fcoord (Mf u).b (Mf u).X v (incl u x) = (Vr u v).mulVec (Formalism.HermitianLatticesTheory.fcoord (M u).b (M u).X v x)

  rank_full : ∀ u, (Fintype.card (Mf u).ι : ℝ) = dstar u * ((T u : ℝ) ^ k - 1) ^ f
  dstar_pos : ∀ u, 0 < dstar u

  rank_ram : ∀ u, (Fintype.card (M u).ι : ℝ) = (Fintype.card (Mf u).ι : ℝ) * (1 - 1 / ((T u : ℝ) - 1)) ^ f
  rank_pos : ∀ u, 0 < Fintype.card (M u).ι

  slope_ram : ∀ u, (M u).mu = (Mf u).mu - (f : ℝ) * Real.log ((T u : ℝ) - 1) / ((T u : ℝ) - 2)

  slopeMax_ram : ∀ u, (M u).muMax ≤ (Mf u).muMax

  Nlam_le : ∀ u w, prW w = T u → atW w (Nlam u w) ≤ atW w (M u).L

  Nlam_bar : ∀ u w, prW w = T u → ¬ overPi u w → atW w (Nlam u w) = atW w (M u).L

  Nlam_len : ∀ u w, prW w = T u →
    ((lenUW w (M u).L (Nlam u w) : ℚ) : ℝ) ≤ (Fintype.card (Mf u).ι : ℝ) * lamT u
  lamT_nonneg : ∀ u, 0 ≤ lamT u

  Nu_fg : ∀ u, (Nu u).FG

  Nu_comm : ∀ u, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ (M u).L, c • y ∈ Nu u

  Nu_atT : ∀ u w, prW w = T u → atW w (Nu u) = atW w (Nlam u w)

  Nu_off : ∀ u w, w ∉ supp → atW w (Nu u) = atW w (M u).L

  Nu_le_ItM : ∀ u, Nu u ≤ toColObj.ItM u

  tau_nonneg : ∀ w, 0 ≤ tau w

  tau_eq_zero_at_T : ∀ u w, prW w = T u → tau w = 0

  supp_alt : ∀ u w, prW w = T u → w ∈ supp

  supp_sat : ∀ w ∈ supp, ∀ w', prW w' = prW w → w' ∈ supp

  propZ_low : ∀ u, zLow u ≤ (Mf u).mu

  propZ_up : ∀ u, (Mf u).muMax ≤ zUp u
  Dstar_pos : 0 < Dstar
  Xu_pos : ∀ u, 0 < Xu u

  Xu_pow : ∀ u, Xu u ^ (f * k) = Dstar / dstar u
  log_height_lower_bound : ∀ u, xLow ≤ Real.log (Xu u)
  log_height_upper_bound : ∀ u, Real.log (Xu u) ≤ xUp
  log_height_variation_bound : ∀ u u', |Real.log (Xu u) - Real.log (Xu u')| ≤ xVar

  Mtil_good : Mtil.Good

namespace ColIface

end ColIface

section Glue

variable {K : Type} [Field K] [NumberField K]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem exists_smul_le_of_lattice {M N : Submodule (𝓞 K) V} (hM : M.FG) (hN : Submodule.IsLattice K N) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  have key : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span K (N : Set V) := by rw [hN.span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, h1⟩ := hy
      obtain ⟨d, hd, h2⟩ := hz
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      have e1 : (c * d) • y = d • (c • y) := by rw [mul_comm, mul_smul]
      have e2 : (c * d) • z = c • (d • z) := mul_smul c d z
      rw [smul_add, e1, e2]
      exact N.add_mem (N.smul_mem d h1) (N.smul_mem c h2)
    | smul a y _ hy =>
      obtain ⟨c, hc, h1⟩ := hy
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
      refine ⟨c * d, mul_ne_zero hc (nonZeroDivisors.ne_zero d.2), ?_⟩
      have h2 : ((d : 𝓞 K)) • (a • y) = n • y := by
        rw [← algebraMap_smul K (d : 𝓞 K) (a • y), smul_smul, mul_comm, hnd, algebraMap_smul]
      rw [mul_smul, h2, smul_comm]
      exact N.smul_mem n h1
  obtain ⟨s, hs⟩ := hM
  classical
  choose c hc hcs using key
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc x, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s c hx, mul_comm, mul_smul]
    exact N.smul_mem _ (hcs x)
  | zero => rw [smul_zero]; exact N.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact N.smul_mem a hy

end Glue

structure ScNum where

  sc : Formalism.BasicNotions.Scale

  Sc : ℝ

  C0 : ℝ

  eta : ℝ

def ScNum.CY (_ : ScNum) : ℝ := 9

@[simp] theorem ScNum.CY_eq (n : ScNum) : n.CY = 9 := rfl

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def lamRowC (S : RowPar R) : Fin R.r → ℝ := fun i =>
  if h : i.val < R.k - 1 then (S.v ⟨i.val, h⟩ : ℝ)
  else if h' : i.val - (R.k - 1) < R.m then -(S.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) else 0

theorem lamRowC_of (P : HCParam R) : lamRowC (RowPar.of P) = Formalism.MainNotions.S.lamS R P := rfl

theorem iface_strictAnti_of_succ {n : ℕ} (f : Fin n → ℝ)
    (h : ∀ (i : ℕ) (hi : i + 1 < n), f ⟨i + 1, hi⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change a < b at hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact lt_trans (h b hb) (ih (by omega) h1)
    · subst h1; exact h a hb

theorem lamRowC_strictAnti (P : HCParam R) : StrictAnti (lamRowC (RowPar.of P)) := by
  apply iface_strictAnti_of_succ
  intro i hi
  have hr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  simp only [lamRowC, RowPar.of]
  by_cases h1 : i + 1 < R.k - 1
  · rw [dif_pos h1, dif_pos (show i < R.k - 1 by omega)]
    have a1 := P.u_gt_v ⟨i + 1, h1⟩
    have a2 := P.v_gt_u ⟨i, by omega⟩
    exact_mod_cast lt_trans a1 a2
  · by_cases h2 : i < R.k - 1
    · rw [dif_neg h1, dif_pos (show i + 1 - (R.k - 1) < R.m by omega), dif_pos h2]
      have a1 := P.u_last_gt (by omega) (by omega)
      have a2 := P.v_gt_u ⟨i, h2⟩
      have e1 : P.u ⟨i + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := congrArg P.u (Fin.ext (by simp; omega))
      have e2 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩ := congrArg P.b (Fin.ext (by simp; omega))
      rw [e2]
      rw [e1] at a2
      have a3 : -P.b ⟨0, by omega⟩ < P.v ⟨i, h2⟩ := lt_trans a1 a2
      exact_mod_cast a3
    · rw [dif_neg h1, dif_neg h2, dif_pos (show i + 1 - (R.k - 1) < R.m by omega),
        dif_pos (show i - (R.k - 1) < R.m by omega)]
      have j1 := P.gap_be ⟨i - (R.k - 1), by omega⟩
      have j2 := P.gap_eb ⟨i - (R.k - 1), by omega⟩ (by simp; omega)
      have e3 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨i - (R.k - 1) + 1, by omega⟩ :=
        congrArg P.b (Fin.ext (by simp; omega))
      rw [e3]
      have h3 : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
      have a4 : P.b ⟨i - (R.k - 1), by omega⟩ < P.b ⟨i - (R.k - 1) + 1, by omega⟩ := by linarith
      have a5 : (P.b ⟨i - (R.k - 1), by omega⟩ : ℝ) < (P.b ⟨i - (R.k - 1) + 1, by omega⟩ : ℝ) := by exact_mod_cast a4
      linarith

def dsigC (τ : X.Tau) : ℝ := Formalism.QuantumDeterminants.fdegHC (lamRowC (W.row τ))

theorem lamSH_isHCParam {R : Ranks} (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.S.lamSH R P) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h := lamRowC_strictAnti P (a := Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) (b := Fin.cast (Formalism.MainNotions.S.dimS_eq R) b)
      hab
    rw [lamRowC_of] at h
    exact h
  · obtain ⟨k', hk'⟩ := R.k_even
    have hn : (((2 * R.rS + R.k + 1 : ℕ) : ℝ) - 1) / 2 = (R.rS : ℝ) + (k' : ℝ) := by
      rw [hk']; push_cast; ring
    rw [hn]
    simp only [Formalism.MainNotions.S.lamSH, Formalism.MainNotions.S.lamS]
    split_ifs with h1 h2
    · obtain ⟨z, hz⟩ := P.v_int ⟨(Fin.cast (Formalism.MainNotions.S.dimS_eq R) a).val, h1⟩
      refine ⟨z - R.rS - k', ?_⟩
      rw [hz]; push_cast; ring
    · obtain ⟨z, hz⟩ := P.b_int ⟨(Fin.cast (Formalism.MainNotions.S.dimS_eq R) a).val - (R.k - 1), h2⟩
      refine ⟨-z - R.rS - k', ?_⟩
      rw [hz]; push_cast; ring
    · exact ⟨-(R.rS : ℤ) - k', by push_cast; ring⟩

structure ColArg where

  num : ScNum

  served : Finset ℕ

  tauP : ℕ → ℕ

  yM : ∀ u, HeightOneSpectrum (𝓞 X.K) → Submodule (𝓞 X.K) (MfV W Ch u)

  supp : Finset (HeightOneSpectrum (𝓞 X.K))

  sg : Pr.Word → HeightOneSpectrum (𝓞 X.K) → ℝ

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)

  Sq : Set ℕ

variable {W Ch} (hX : X.Ok) (A : ColArg W Ch)

def ColArg.dsig (_ : ColArg W Ch) : X.Tau → ℝ := dsigC W

theorem ColArg.dsig_eq : A.dsig = dsigC W := rfl

end Conc

end Formalism.L2.Col
