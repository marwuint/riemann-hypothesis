import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.TiesAsm
import Formalism.SharpRestriction.GrowthBounds.DefsInst

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

def gdOf (R : Ranks) : GC.GD := ⟨R, ⟨∅, ∅, 0, fun _ => PrimeClass.splitK⟩, fun _ => 0⟩

def glOf (R : Ranks) (sc : Scale) (Sc eta : ℝ) : GC.GParameters (gdOf R) := ⟨sc, Sc, eta⟩

def kapSetV (R : Ranks) (sc : Scale) (Sc : ℝ) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    Set ℝ :=
  {κ | 0 ≤ κ ∧
    ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
      [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
      UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      ∀ lam0 : Fin n' → Fin (R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊4 * Sc⌋₊ lam0 → IsDominant lam0 →
        LPprime (W := W) p n' ι σ w 1 lam0 ⌈GC.tIf K (glOf R sc Sc 0) p n' TT a b⌉₊ (GC.DIf K (glOf R sc Sc 0) p n') κ
          (8 * (GC.DIf K (glOf R sc Sc 0) p n' + 1))}

theorem kapISet_eq {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    kapISet L K p n' TT a b = kapSetV D.R L.sc L.Sc K p n' TT a b := rfl

end Formalism.MainNotions.Inhab

end
