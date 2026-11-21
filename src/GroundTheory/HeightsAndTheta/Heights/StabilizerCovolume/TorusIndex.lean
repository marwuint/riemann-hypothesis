import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

section Torus

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def baseChangeLat (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 Em) (Fin N → Em)) :
    Submodule (𝓞 K) ((Em →+* K) → Fin N → K) :=
  Submodule.span (𝓞 K) ((fun v σ a => σ (v a)) '' (I : Set (Fin N → Em)))

open Classical in

def eigenLat (I : Submodule (𝓞 Em) (Fin N → Em)) (s : Em →+* K) : Submodule (𝓞 K) (Fin N → K) :=
  (baseChangeLat K I).comap (LinearMap.single (𝓞 K) (fun _ : Em →+* K => Fin N → K) s)

def familyLat (s : Em →+* K) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) (Set.range fun a i => s (v a i))

def genIndex {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M) : ℝ :=
  (Q.relIndex P : ℝ) / (P.relIndex Q : ℝ)

def familyIndex (I : Submodule (𝓞 Em) (Fin N → Em)) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : ℕ :=
  (Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup

end Torus

def TorusIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (eigenLat I s).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

namespace Gauss

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
