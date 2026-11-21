import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsAsmHformSmulRight
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.StatementMass
import Mathlib

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG Formalism.UG.CS Formalism.UG.P

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem coe_algebraMap_int (d : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

end Loc

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def inclAd : 𝔸 →+* 𝒜 := (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜).toRingHom

theorem inclAd_apply (a : 𝔸) : inclAd (E := E) a = (1 : E) ⊗ₜ[F] a := rfl

end Main

end Formalism.MainNotions.Gaps.CC.Surj
