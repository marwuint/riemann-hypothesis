import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaIsoLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace Uniformity

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

def annSeminorm : RingSeminorm (T.Econ ρ0) where
  toFun b := max (T.gaussSeminorm ρ0 σ0 b) (T.gaussSeminorm ρ0 (topRad ρ0) b)
  map_zero' := by simp
  add_le' a b := max_le
    (((T.gaussSeminorm ρ0 σ0).add_le' a b).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (((T.gaussSeminorm ρ0 (topRad ρ0)).add_le' a b).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _)))
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have h0 : ∀ (f : RingSeminorm (T.Econ ρ0)) (x : T.Econ ρ0), 0 ≤ f x := fun f x => apply_nonneg f x
    refine max_le (((T.gaussSeminorm ρ0 σ0).mul_le' a b).trans ?_)
      (((T.gaussSeminorm ρ0 (topRad ρ0)).mul_le' a b).trans ?_)
    · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))

abbrev AnnRad := Set.Icc ((σ0 : ℝ)) (ρ0 : ℝ)

variable {ρ0 σ0} in

def annIoc (r : AnnRad ρ0 σ0) : Set.Ioc (0 : ℝ) ρ0 := ⟨r, σ0.2.1.trans_le r.2.1, r.2.2⟩

@[simp] theorem coe_annIoc {r : AnnRad ρ0 σ0} : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = r := rfl

def annIn : AnnRad ρ0 σ0 := ⟨σ0, le_rfl, σ0.2.2⟩

def annOut : AnnRad ρ0 σ0 := ⟨ρ0, σ0.2.2, le_rfl⟩

@[simp] theorem coe_annIn : ((annIn ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = σ0 := rfl

@[simp] theorem coe_annOut : ((annOut ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = ρ0 := rfl

variable {ρ0 σ0} in

theorem gaussNorm_le_annSeminorm (b : T.Econ ρ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB b) r ≤ T.annSeminorm ρ0 σ0 b :=
  gaussNorm_le_max σ0.2.1 r.2.1 r.2.2 (T.convergesAt_rad ρ0 b σ0) (T.convergesAt_rad ρ0 b (topRad ρ0))

@[nolint unusedArguments]
def AnnCore (_σ0 : Set.Ioc (0 : ℝ) ρ0) : Type _ := T.Econ ρ0

instance : CommRing (T.AnnCore ρ0 σ0) := inferInstanceAs (CommRing (T.Econ ρ0))

instance : PseudoMetricSpace (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toSeminormedRing.toPseudoMetricSpace

instance : IsUniformAddGroup (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup

instance : IsTopologicalRing (T.AnnCore ρ0 σ0) := by
  have : ContinuousMul (T.AnnCore ρ0 σ0) :=
    @NonUnitalSeminormedRing.toContinuousMul _
      (T.annSeminorm ρ0 σ0).toSeminormedRing.toNonUnitalSeminormedRing
  exact {}

abbrev Ann := UniformSpace.Completion (T.AnnCore ρ0 σ0)

def coreOf : T.Econ ρ0 →+* T.AnnCore ρ0 σ0 := RingHom.id (T.Econ ρ0)

def coreVal (b : T.AnnCore ρ0 σ0) : T.B := ((show T.Econ ρ0 from b) : T.B)

variable {ρ0 σ0}

@[simp] theorem coreVal_coreOf (b : T.Econ ρ0) : T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b) = b := rfl

variable (ρ0 σ0) in

def annNorm (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) : ℝ :=
  Completion.extension (fun b : T.AnnCore ρ0 σ0 => gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r) x

section Res

variable {ρ1 : Set.Ioo (0 : ℝ) 1} (σ1 : Set.Ioc (0 : ℝ) ρ1) (h : (ρ1 : ℝ) ≤ ρ0)

variable {σ1} in

def annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) : AnnRad ρ0 σ0 :=
  ⟨r, hσ.trans r.2.1, r.2.2.trans h⟩

variable {σ1} in
@[simp] theorem coe_annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) :
    ((annRadOf h hσ r : AnnRad ρ0 σ0) : ℝ) = r := rfl

variable {σ1} (hσ : (σ0 : ℝ) ≤ σ1)

end Res

namespace TeichFrob

variable {T} (F : T.TeichFrob)

def annPowRad (r : AnnRad ρ0 σ0) : AnnRad (F.powRadius ρ0) (F.powRad σ0) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_le_pow_left₀ σ0.2.1.le r.2.1 _, pow_le_pow_left₀ (σ0.2.1.trans_le r.2.1).le r.2.2 _⟩

@[simp] theorem coe_annPowRad (r : AnnRad ρ0 σ0) :
    ((F.annPowRad r : AnnRad (F.powRadius ρ0) (F.powRad σ0)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

end TeichFrob

namespace TeichIso

variable {T} (G : T.TeichIso)

def coreMap : T.AnnCore ρ0 σ0 →+* T.AnnCore ρ0 σ0 := G.econMap ρ0

end TeichIso

end TeichLift

end GroundTheory.PAdicHodge
