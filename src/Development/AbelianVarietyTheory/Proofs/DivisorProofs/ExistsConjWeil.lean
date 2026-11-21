import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ConjWeil

theorem hecke_mul_inv {D : D7} {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem exists_of_datum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (ho : IsWeilDatumO ψ S T χS χT om)
    (hS : IsHeckeChar D χS') (hT : IsHeckeChar D χT') (rS : ResEta D χS' S.rank) (rT : ResEta D χT' T.rank) :
    ∃ om', IsWeilDatumO ψ S T χS' χT' om' := by
  obtain ⟨o, h1, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (hecke_mul_inv hS ho.hecS) (hecke_mul_inv hT ho.hecT)
    (resEta_parity (resEta_mul rS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul rT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  exact ⟨o, h1⟩

theorem even_im_hermitian_sub (R : Ranks) : 0 % 2 = R.nV % 2 ∧ (0 + 1) % 2 = R.r % 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have h2 := R.two_le_m
  unfold Ranks.nV Ranks.r
  constructor <;> omega

end GlobalTheory.GalLift.ConjWeil
