import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

namespace Ad3P.DihedralUnramifiedPlaces

def toH (η : HeckeCharacter ℚ) : Formalism.L2.Host.HChar ℚ :=
  ⟨Circle.toUnits.comp η.toIdele, by
    refine ⟨?_, fun k => ?_⟩
    · refine Units.continuous_iff.2 ⟨continuous_subtype_val.comp η.continuous_toIdele, ?_⟩
      have h : (fun x => ((((Circle.toUnits.comp η.toIdele) x)⁻¹ : ℂˣ) : ℂ)) =
          fun x => (((Circle.toUnits.comp η.toIdele) x⁻¹ : ℂˣ) : ℂ) := by
        funext x
        rw [map_inv]
      rw [h]
      exact continuous_subtype_val.comp (η.continuous_toIdele.comp continuous_inv)
    · exact (congrArg Circle.toUnits (η.toIdele_diagonal k)).trans (map_one _)⟩

theorem ord_eq (v : Ad3.Pl) {x : Ad3.Qv v} (hx : x ≠ 0) : ord x = -WithZero.log (Valued.v x) := by
  have h1 := norm_eq_absNorm_zpow_neg_ord v hx
  have h2 := normalizedAbv_eq_zpow v hx
  rw [normalizedAbv_apply] at h2
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal v
  have := zpow_right_injective₀ (by linarith) hq.ne' (h1.symm.trans h2)
  omega

theorem loc_eq (η : HeckeCharacter ℚ) (v : Ad3.Pl) (x : (Ad3.Qv v)ˣ) : (toH η).loc v x = localChar η v x := rfl

end Ad3P.DihedralUnramifiedPlaces
