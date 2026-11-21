import CompanionTheory.AutomorphicTheory.SegmentRepresentations.RapidDecayFamilies.MirabolicColumnBlock
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.JacquetShalikaBounds.FormQuasiInvariantMirabolic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace CompanionTheory.jumpWindows

abbrev Pl (E : Type) [Field E] [NumberField E] : Type := HeightOneSpectrum (𝓞 E)

abbrev XB (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := GA E a →ᵇ ℂ

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def rtFun (h : GA E a) (φ : XB E a) : XB E a := φ.compContinuous ⟨fun g => g * h, continuous_mul_right h⟩

variable (E a) in

def Rt : GA E a →* (XB E a →L[ℂ] XB E a) where
  toFun h := LinearMap.mkContinuous
    { toFun := rtFun h, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    fun φ => by rw [one_mul]; exact norm_compContinuous_le _ _
  map_one' := by ext φ g; change φ (g * 1) = φ g; rw [mul_one]
  map_mul' h k := by ext φ g; change φ (g * (h * k)) = φ (g * h * k); rw [mul_assoc]

@[simp] theorem Rt_apply (h g : GA E a) (φ : XB E a) : Rt E a h φ g = φ (g * h) := rfl

def fl (a : ℕ) (w : Pl E) : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)

def cLoc (w : Pl E) : GA E a →* GL (Fin a) (w.adicCompletion E) :=
  GeneralLinearGroup.map ((pLoc E w).comp (pFin E))

def repW (a : ℕ) (w : Pl E) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (XB E a) :=
  (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (Rt E a)).comp (fl a w)

@[simp] theorem repW_apply (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)) (φ : XB E a) :
    repW a w u φ = Rt E a (fl a w u) φ := rfl

def InS (S : Finset (Pl E)) (g : GA E a) : Prop := ∀ w, w ∉ S → cLoc w g = 1

structure YOK (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) (Y : Submodule ℂ (XB E a)) : Prop where
  closed : IsClosed (Y : Set (XB E a))
  stable : ∀ g, InS S g → ∀ φ ∈ Y, Rt E a g φ ∈ Y
  good : ∀ φ ∈ Y, Good ψ (a - 1) φ

variable [IsTotallyComplex E]

end CompanionTheory.jumpWindows

end
