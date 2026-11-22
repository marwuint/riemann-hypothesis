import Formalism.LocalToGlobal.IndefiniteReal.DatumF

noncomputable section

open MeasureTheory

namespace Formalism.IndefR.LiftF

section Step

variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]

def liftInt (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (s : S) (F : H → ℂ) (g : G) : ℂ :=
  ∫ h in 𝓕, th g h s * F h ∂ν

structure IsIo (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt) : Prop where

  integ : ∀ F : CCs, ∀ φ v g,
    IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν

  eq : ∀ F : CCs, ∀ φ v g,
    liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g = ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g

end Step

section ThetaP

variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

def thetaPInt (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (f : H' → Tau) (e : TK) (g : G') : ℂ :=
  ∫ h in 𝓕, th g h (pt (io e (f h))) ∂ν

structure IsThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (A : Submodule ℂ (H' → Tau))
    (thP : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))) : Prop where

  integ : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν

  eq : ∀ f : A, ∀ e g, thP f e g = thetaPInt ν 𝓕 th pt io f e g

variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]

end ThetaP

section Kernels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (xi0 : E)

variable (F) in

def intAfF : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

variable (F E) in

def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAfF F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

end Kernels

end Formalism.IndefR.LiftF

end
