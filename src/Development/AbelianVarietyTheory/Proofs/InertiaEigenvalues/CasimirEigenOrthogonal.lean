import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrix

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

open Classical in

def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
