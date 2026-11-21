import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose_spec

section Shrink
variable (R : Type) [CommRing R] (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B)

abbrev LS : Type := Localization.Away (algebraMap B A' s)

theorem rho_unit : IsUnit (((algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp
    (algebraMap A' (LS B A' s))) (algebraMap B A' f)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (LS B A' s) f)) (algebraMap B (LS B A' s) f)
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h

def rho : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B (LS B A' s) f) :=
  IsLocalization.Away.lift (algebraMap B A' f)
    (g := (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap A' (LS B A' s)))
    (rho_unit B A' f s)

end Shrink

end UpperTheory.Deg2
