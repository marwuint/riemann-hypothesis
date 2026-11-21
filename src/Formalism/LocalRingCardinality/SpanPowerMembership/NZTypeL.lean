import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

def etaZ (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) →* ℤˣ :=
  (quadraticChar (ZMod (H.g k))).toUnitHom.comp Matrix.GeneralLinearGroup.det

variable (K : Type) [Field K] [CharZero K]

def psiU (k : Fin 2) (v : Fin R.f) : GL (Fin R.r) (ZMod (H.g k)) →* Kˣ :=
  if v.1 ≠ 0 then (Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k) else 1

variable (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

variable (V : Type) [AddCommGroup V] [Module K V]

end Formalism.BasicNotions.Examples₂.NZ
