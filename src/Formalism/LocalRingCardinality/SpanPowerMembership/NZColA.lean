import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField Formalism.MainNotions.G

structure GatBasis (D : D7) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  bas : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).ι → (D.gat u w hg).Fn
  bas_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (bas u w hg)
  bas_span : ∀ u w hg, Submodule.span (D.gat u w hg).O (Set.range (bas u w hg)) = (D.gat u w hg).M

namespace GatBasis

variable {D : D7} (B : GatBasis D)

def cmp (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn where
  toFun x := ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem cmp_apply (u w hg) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg x = ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a := rfl

end GatBasis

end Formalism.BasicNotions.Examples₂.NZ
