import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Formalism.LocalToGlobal.CharacterGerms.PlugUP

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Rank

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp where
  big_compl := (hr o).1
  rk_big := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.1 g a hb)
  rk_small := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.2 g a hb)

end Rank

end Formalism.L2.FormalSeriesBounds
