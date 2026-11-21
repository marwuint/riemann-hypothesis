import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_le_iff (x p : kˣ) :
    ValuativeRel.valuation k (x : k) ≤ ValuativeRel.valuation k (p : k) ↔ ord (p : k) ≤ ord (x : k) := by
  have h := mem_valBall_iff_le_ord (n := 0) (x * p⁻¹ : kˣ).ne_zero
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff, ord_units_mul, ord_units_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    mul_inv_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 p.ne_zero)), one_mul] at h
  rw [h]
  omega

end Loc

