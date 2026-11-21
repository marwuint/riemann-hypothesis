import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def MonoAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p r : ℕ) [NeZero r] {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (b : SegBlock s r) (m m' : ℝ), m ≤ m' →
    (blockData p S aTop aPlus m' b).SSZ O (r := r) ≤ (blockData p S aTop aPlus m b).SSZ O (r := r)

def PlaneAt : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (m : ℕ) (φ : WF p n' ≃+* W) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e e' : Edge W Qq (m + 1)), IsFractionRing W Qq →
    IsGLW g → IsGLW g' → IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    IsEdgeBasis p 1 e' (h * ((matQ φ g')⁻¹).transpose) → ratPlane p n' 1 g' = ratPlane p n' 1 g → e' = e

def SymIntAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
    (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)).SSZ O
      (r := X.m)) →
    InA (O := O) (symFam (KK O) X.p C0 CE1 CE2 X β s)

theorem scale_one_mem {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {M : Submodule O V} {x : V} (hx : x ∈ scale (1 : Kf) M) : x ∈ M := by
  simp only [scale, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

end Formalism.MainNotions.ColumnSystems.Pf
