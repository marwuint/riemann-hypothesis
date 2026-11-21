import Mathlib
import ReciprocityTheory.DualLattices.SeriesState

noncomputable section

open TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing

universe u

variable {R₀ : Type u} [CommRing R₀]

theorem isLocalRing_dualNumber (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := inferInstanceAs (Nontrivial (A × A))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

def dual (R : LAlg R₀) : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R) _ _ (isLocalRing_dualNumber R)

def eta (R : LAlg R₀) : dual R := (DualNumber.eps : DualNumber R)

def red (R : LAlg R₀) : LHom (dual R) R :=
  ⟨TrivSqZeroExt.fstHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

def incl (R : LAlg R₀) : LHom R (dual R) :=
  ⟨TrivSqZeroExt.inlAlgHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_inl_iff.1 h⟩⟩

theorem red_comp_incl (R : LAlg R₀) : (red R).comp (incl R) = LHom.id R :=
  Subtype.ext (AlgHom.ext fun _ => rfl)

theorem eta_mul_eta (R : LAlg R₀) : eta R * eta R = 0 := DualNumber.eps_mul_eps

theorem red_sqZero (R : LAlg R₀) : (red R).SqZero := by
  refine LHom.sqZero_of_span _ (eta R) (fun a => ⟨(incl R).1 a, rfl⟩) ?_ (eta_mul_eta R)
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hx
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst b = 0 →
        (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber R) * DualNumber.eps = b :=
      fun b hb => by ext <;> simp [hb]
    exact ⟨_, key x hx⟩
  · rintro ⟨a, rfl⟩
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst (b * DualNumber.eps) = 0 := fun b => by simp
    exact key a

variable (B : BX R₀)

end GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing
