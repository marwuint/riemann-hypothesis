import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTraceTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fn_ext_of_surjective {W Y : Scheme.{0}} (Ψ : W ⟶ Y) [Surjective Ψ] [IsReduced Y] {U : Y.Opens}
    {a b : Γ(Y, U)} (h : ∀ w, Ψ w ∈ U → gs Ψ w U a = gs Ψ w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨w, rfl⟩ := Ψ.surjective y
  have hU : Ψ w ∈ U := Y.basicOpen_le _ hy
  have hw : w ∈ W.basicOpen ((Ψ.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hy
  rw [W.mem_basicOpen _ w hU] at hw
  have e := h w hU
  rw [gs_eq _ _ _ hU, gs_eq _ _ _ hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  exact absurd (e ▸ hw) not_isUnit_zero

theorem sec_eq_of_surjective {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {T : Over S} {W : Scheme.{0}}
    (Ψ : W ⟶ (T ⊗ A).left) [Surjective Ψ] [IsReduced (T ⊗ A).left] {k : ℤ} {u v : LB.Sec (LPow A L.L k T)}
    (h : ∀ w J, Good L.L w J → sv A L u Ψ w J = sv A L v Ψ w J) : u = v := by
  refine sec_ext fun j => fn_ext_of_surjective Ψ fun w hw => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB w (fun _ : Fin 1 => Ψ ≫ (snd T A).left) j
    (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => Set.mem_iInter.1 hw k)
  exact (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) u Ψ w J j e).symm.trans
    ((h w J hJ).trans (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) v Ψ w J j e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.ThetaTraceTest
