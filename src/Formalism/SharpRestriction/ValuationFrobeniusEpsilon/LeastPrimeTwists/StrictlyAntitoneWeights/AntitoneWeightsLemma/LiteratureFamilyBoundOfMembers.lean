import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeHeightBounds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain

namespace Formalism.MainNotions.V.Pf.V3.LG

open Formalism.MainNotions.UnitaryThreeHeightBounds

variable {D : D7} (V : VData D)

def LocGlob3Pt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    UnitaryThreeData V l e χ K → ∀ g1 : GQ, IsNormElt V l e χ K g1 → UnitaryThreeFiniteness V l e χ K g1 →
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    Continuous (V.rho3 ξ) → IsCSDOne (VData.toRecRep (V.rho3 ξ)) →
    ∀ M : ℕ, 0 < M → condV D ∣ M → OrdFixAbove (VData.toRecRep (V.rho3 ξ)) ![(e : ℤ), 0, -(e : ℤ)] M →
    Ram3 V l K (V.rho3 ξ) M →
    ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π → ∀ (ι : QbarL l ≃+* ℂ) (j : ℤ),
    (∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = -(![(e : ℤ), 0, -(e : ℤ)] : Fin 3 → ℤ) i.rev - j) →
    IsRiAt V ι π (VData.toRecRep (twistRep (V.rho3 ξ) (((epsL l).comp K.fixingSubgroup.subtype) ^ j))) →
    (V.spec K 3).level π M

variable {V}

variable (D V)

variable {D V}

end Formalism.MainNotions.V.Pf.V3.LG
