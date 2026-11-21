import Formalism.LocalRingCardinality.SpanPowerMembership.EmbeddingBaseFieldCondition

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (E : EmbC D C)

section One

variable (M : HLat D.what₂.LL) (w : D.what₂.places.Pl) (j : ℕ) (eI : I.ix j → M.ι)

abbrev vE : (I.ix j → FractionRing (C.Ok (E.twI w) 1)) ≃ₗ[C.Ok (E.twI w) 1]
    (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) :=
  vecE (C.O (E.twI w)) (C.Ok (E.twI w) 1) (I.ix j) (C.Ok_inj (E.twI w) 1)

def crd (x : M.V) : I.ix j → FractionRing (C.Ok (E.twI w) 1) := fun a => E.embW w (M.b.repr x (eI a))

def eMjN : M.V →+ (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) where
  toFun x := vE D C I E w j (crd D C I E M w j eI x)
  map_zero' := by
    have : crd D C I E M w j eI 0 = 0 := funext fun a => by simp [crd]
    rw [this, map_zero]
  map_add' x y := by
    have : crd D C I E M w j eI (x + y) = crd D C I E M w j eI x + crd D C I E M w j eI y :=
      funext fun a => by simp [crd]
    rw [this, map_add]

theorem eMjN_apply (x : M.V) : eMjN D C I E M w j eI x = vE D C I E w j (crd D C I E M w j eI x) := rfl

variable (hb : Function.Bijective eI)

end One

end Formalism.BasicNotions.Examples₂.NZ
