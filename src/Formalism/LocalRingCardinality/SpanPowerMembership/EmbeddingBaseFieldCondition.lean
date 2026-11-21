import Formalism.LocalRingCardinality.SpanPowerMembership.RangeInclEqSpan
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Coord

variable {K F W ι : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]
  (σ : K →+* F) (b : Module.Basis ι K W)

def coordMap : W →ₛₗ[σ] (ι → F) where
  toFun x a := σ (b.repr x a)
  map_add' x y := funext fun a => by simp
  map_smul' c x := funext fun a => by simp

theorem coordMap_apply (x : W) (a : ι) : coordMap σ b x a = σ (b.repr x a) := rfl

end Coord

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

set_option synthInstance.maxHeartbeats 400000 in

structure EmbC where
  twI : D.what₂.places.Pl → C.Tw
  twI_l : ∀ w, C.l (twI w) = D.what₂.places.resChar w
  embW : ∀ w, D.what₂.LL →+* FractionRing (C.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))).range
  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : C.O0 (twI w)), z ≠ 0 →
    C.emb0 (twI w) x * algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) z =
      algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) y →
    embW w (x : D.what₂.LL) * algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) z)) =
      algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) y))

variable (E : EmbC D C)

structure StdMt where
  bT : ∀ w j, Module.Basis (I.ixM j) D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  bT_gen : ∀ w j, {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen} = Set.range (bT w j)

variable (S : StdMt D C I)

end Formalism.BasicNotions.Examples₂.NZ
