import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

noncomputable section
namespace Formalism.MainNotions.Gaps.LevGap
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section DefCong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

def CongAt (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (g : GL n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, ∃ s ∈ intV E v, (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
    (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j = (c : E ⊗[F] v.adicCompletion F) * s

end DefCong

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [TopologicalSpace R] [IsTopologicalRing R]

local instance topT : TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

local instance modT : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩

variable [FiniteDimensional F E]

end Gen

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem compact_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

theorem isCompact_intAd : IsCompact (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := compact_Ov
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_intAd : IsOpen (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open scoped RestrictedProduct in
theorem t2Space_adeleRing_numberField : T2Space 𝔸 :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance topT' (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL n A) (i j : n) :
    (bc φ g : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl

end Main

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

section Loc

variable (v : HeightOneSpectrum (𝓞 F))

theorem CongAt.mono {c c' : ℕ} (h : c' ∣ c) {g : GL n (E ⊗[F] v.adicCompletion F)}
    (hg : CongAt v c g) : CongAt v c' g := by
  obtain ⟨e, rfl⟩ := h
  intro i j
  obtain ⟨s, hs, he⟩ := hg i j
  exact ⟨(e : E ⊗[F] v.adicCompletion F) * s, mul_mem (natCast_mem _ e) hs, by
    rw [he, Nat.cast_mul, mul_assoc]⟩

end Loc

end Bridge

end Formalism.MainNotions.Gaps.LevGap
