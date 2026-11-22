import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

section Mod

section Wt

variable {D : D7} {j : ℕ}

theorem wt_ext {w w' : WeightFamilies.Wt D j} (hP : w.aP = w'.aP) (hM : w.aM = w'.aM) (hn : w.n = w'.n) : w = w' := by
  cases w; cases w'; simp only at hP hM hn; subst hP hM hn; rfl

instance wtAdd (D : D7) (j : ℕ) : Add (WeightFamilies.Wt D j) := ⟨wadd⟩

instance wtZero (D : D7) (j : ℕ) : Zero (WeightFamilies.Wt D j) := ⟨wt0 D j⟩

instance wtACM (D : D7) (j : ℕ) : AddCommMonoid (WeightFamilies.Wt D j) where
  add_assoc a b c := wt_ext (by funext τ i; exact Nat.add_assoc _ _ _) (by funext τ i; exact Nat.add_assoc _ _ _)
    (Nat.add_assoc _ _ _)
  zero_add a := wt_ext (by funext τ i; exact Nat.zero_add _) (by funext τ i; exact Nat.zero_add _) (Nat.zero_add _)
  add_zero a := wt_ext (by funext τ i; exact Nat.add_zero _) (by funext τ i; exact Nat.add_zero _) (Nat.add_zero _)
  add_comm a b := wt_ext (by funext τ i; exact Nat.add_comm _ _) (by funext τ i; exact Nat.add_comm _ _) (Nat.add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

end Wt

section Val

variable {K : Type} [Field K] [NumberField K]

def vE (la : HeightOneSpectrum (𝓞 K)) (x : K) : EReal :=
  open Classical in if x = 0 then ⊤ else (((vAdd la x : ℤ) : ℝ) : EReal)

end Val

section Model

variable (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O)
  (Sg : ∀ j, WeightFamilies.Wt D j → Prop)

def cuspS (p : Prop) : Submodule K K := open Classical in if p then ⊤ else ⊥

def mlatS (p : Prop) : Submodule (𝓞 K) ↥(cuspS K p) :=
  (LinearMap.range (Algebra.linearMap (𝓞 K) K)).comap ((cuspS K p).subtype.restrictScalars (𝓞 K))

abbrev provS : WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun j w => ↥(cuspS K (Sg j w))
  Mlat := fun j w => mlatS K (Sg j w)
  supN := fun _ _ σ F => ‖σ (F : K)‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  supN_smul := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ (F : K)‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  l2Norm_smul_alt := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0

variable {D K Sg}

def oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : (provS D K e Sg).Cusp j w :=
  ⟨1, by simp [cuspS, h]⟩

variable (K) in

def sWS {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 K := ((qq D ^ DF w : ℕ) : 𝓞 K)

def evS (j : ℕ) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₐ[K] K := AddMonoidAlgebra.lift K K (WeightFamilies.Wt D j) 1

def incS (j : ℕ) (w : WeightFamilies.Wt D j) : (provS D K e Sg).Cusp j w →ₗ[K] AddMonoidAlgebra K (WeightFamilies.Wt D j) where
  toFun F := AddMonoidAlgebra.single w (F : K)
  map_add' F G := by rw [Submodule.coe_add, AddMonoidAlgebra.single_add]
  map_smul' c F := by rw [Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, AddMonoidAlgebra.smul_single']

def coefS (j : ℕ) (w : WeightFamilies.Wt D j) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₗ[K] K where
  toFun F := F.coeff w
  map_add' F G := by rw [AddMonoidAlgebra.coeff_add]; rfl
  map_smul' c F := by rw [AddMonoidAlgebra.coeff_smul]; rfl

variable (Sg)

end Model

section Lemmas

variable {D : D7} {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) {Sg : ∀ j, WeightFamilies.Wt D j → Prop}
  (hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w')) (P : ModuliIntegralCharts.Prov D) {j : ℕ} (dat : P.Dat)
  (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1)
  (hPt : ∀ p, Nonempty ((P.loc dat p).Pt (P.loc dat p).YY))

end Lemmas

end Mod

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

end
