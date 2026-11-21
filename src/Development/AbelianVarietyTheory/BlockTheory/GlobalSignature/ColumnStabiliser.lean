import Mathlib
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Subgroup (GL (Fin D.R.k) D.host.E) :=
  letI := D.host.cmStar
  fun y =>
    UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ⊓
      ((Lv u).U.comap (MulAut.conj (y : GL (Fin D.R.k)
          (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹).toMonoidHom).comap
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem mem_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ (y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin D.R.k) D.host.E),
      γ ∈ colStab D Lv u y ↔
        γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
          (y : GL (Fin D.R.k) _)⁻¹ *
            bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
            (y : GL (Fin D.R.k) _) ∈ (Lv u).U := by
  intro y γ
  simp [colStab, Subgroup.mem_inf, Subgroup.mem_comap]

def ColStabTrivialAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      colStab D Lv u y = ⊥

def ColStabTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), ColStabTrivialAt D Lv u

theorem map_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (colStab D Lv u y).map (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
        ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj (y : GL (Fin D.R.k) _)).toMonoidHom := by
  intro y
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_colStab D Lv u y γ).1 hγ
    exact ⟨⟨γ, h1, rfl⟩, ⟨_, h2, by simp [mul_assoc]⟩⟩
  · rintro ⟨⟨γ, h1, rfl⟩, z, hz, hz'⟩
    refine ⟨γ, (mem_colStab D Lv u y γ).2 ⟨h1, ?_⟩, rfl⟩
    rw [← hz']
    simpa [mul_assoc] using hz

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser
