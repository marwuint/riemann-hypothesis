import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt

variable {D : D7}

open Classical in

def sys (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (x : L.X.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then
    iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x)
  else 0

theorem iotaO_injective (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Function.Injective (iotaO L.X.nd L.Y.naut i) := by
  intro a b h
  unfold iotaO at h
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  exact IsFractionRing.injective (L.X.nd.O i) (FractionRing (L.X.nd.O i))
    ((L.Y.naut.iotaQ i).injective ((L.Y.naut.iotaQC i).injective h))

theorem sys_inj (L : LocAll (lay0 D)) (i : L.X.nd.Loc) {x x' : L.X.nd.X i} (h : sys L i x = sys L i x') : x = x' := by
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := L.X.nd.T_sep i x x' hne
  apply hfx
  let E : Subalgebra (L.X.nd.O i) (L.X.nd.X i → L.X.nd.O i) :=
    AlgHom.equalizer (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x)
      (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x')
  have hle : L.X.nd.T i ≤ E := by
    rw [← L.X.nd.T_gen i, Algebra.adjoin_le_iff]
    rintro g ⟨v, k, hs, hl, hS, hQ, k1, k2, rfl⟩
    have hv : SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV := ⟨⟨hs, hl, hS, hQ⟩, k1, k2⟩
    have := congrFun (congrFun h v) k
    unfold sys at this
    rw [if_pos hv, if_pos hv] at this
    exact iotaO_injective L i this
  exact hle hf

end GlobalTheory.PtExt

end
