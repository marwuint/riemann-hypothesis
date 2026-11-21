import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GrpMain

section
variable {R : Type} [CommRing R] {G : Type} [TopologicalSpace G] [AddCommGroup G]
  {M : Type w} [AddCommGroup M] [Module R M]

def shiftBy [IsTopologicalAddGroup G] (v : G) (n : ℕ) : C(Fin (n + 1) → G, Fin (n + 1) → G) :=
  ⟨fun x j => x j - v, by fun_prop⟩

def tw [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ) :
    (lcCos R G M).cx.X n →ₗ[R] (lcCos R G M).cx.X n where
  toFun f := LocallyConstant.map (ρ (Multiplicative.ofAdd v))
    (LocallyConstant.comap (shiftBy v n) f) - f
  map_add' f g := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (f _ + g _) - (f x + g x) =
      (ρ (Multiplicative.ofAdd v) (f _) - f x) + (ρ (Multiplicative.ofAdd v) (g _) - g x)
    rw [map_add]
    abel
  map_smul' c f := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (c • f _) - c • f x =
      c • (ρ (Multiplicative.ofAdd v) (f _) - f x)
    rw [map_smul, smul_sub]

theorem tw_apply [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) (x : Fin (n + 1) → G) :
    tw ρ v n f x = ρ (Multiplicative.ofAdd v) (f fun j => x j - v) - f x := rfl

end

end GlobalTheory.CompanionTheory.GrpMain
