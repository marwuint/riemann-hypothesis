import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.DataDIVDefs

noncomputable section

namespace GlobalTheory.Survey.IrrationalRotationBlocks

open Formalism.BasicNotions NumberField

def withBk (D : D7) (B : ∀ u, (D.div.Nu u).V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL D.div.RR.V) : D7 :=
  { D with div := { D.div with Bk := B } }

theorem buRational_withBk (D : D7) (B) : (withBk D B).BuRational ↔
    ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
      D.what₂.Bu u (D.jN u φ) (D.jEE x) = D.what₂.embLL (B u φ x) := Iff.rfl

end GlobalTheory.Survey.IrrationalRotationBlocks
