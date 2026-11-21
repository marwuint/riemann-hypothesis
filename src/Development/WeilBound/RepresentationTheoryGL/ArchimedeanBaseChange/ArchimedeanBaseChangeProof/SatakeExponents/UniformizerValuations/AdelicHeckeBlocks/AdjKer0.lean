import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.GelfandEvenSmoothness.IntSmooth

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Sq

end Sq

theorem sqOk (h0 : AdjKer0) (h1 : BlockOperatorsProductAdjoint) (h2 : BlockWordOperators) : SqOk := by
  intro E _ _ _ B t g m ht hg hka hkb
  obtain ⟨-, -, -, -, hadjOk, hadjOp, -, -⟩ := h1 E B t t ht ht
  have hmult : ∀ {n : ℕ} (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : Mods E n) (k : Kers M)
      (va : InfinitePlace E → Inf n → ℂ), (∀ v, IsKer μ (M v) [] g (k v) ∧ ∀ χ, va v χ = coshT g (cas χ)) →
      IsMults μ (adjK k) va t.T := by
    intro n μ hμ M k va h v
    refine ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => adjK k v,
      fun _ => ⟨hg, h0 n μ hμ (M v) g t.T (k v) hg (h v).1⟩, ?_, ?_⟩
    · intro y _
      simp
    · intro χ
      simp [zVal, (h v).2 χ]
  have hadj' : t.adj'.Ok :=
    ⟨ht.T, ht.r, hmult B.μa B.ha B.Ma t.ka t.va hka, hmult B.μb B.hb B.Mb t.kb t.vb hkb, hadjOk.ψ, hadjOk.size⟩
  have hw : ∀ s : PT B, s.Ok → (s.pw m).Ok ∧ (s.pw m).op = s.op ^ (m + 1) ∧
      ∀ χa χb, (s.pw m).val χa χb = s.val χa χb ^ (m + 1) := by
    intro s hs
    obtain ⟨hO, hop, -, -, -, hval⟩ := h2 E B (List.replicate m (Sum.inr s)) s (max s.T (s.r + B.c))
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hs) hs (le_max_of_le_left hs.T)
      (fun s' hs' => by
        cases Sum.inr.inj (List.eq_of_mem_replicate hs')
        exact ⟨le_max_left _ _, le_max_right _ _⟩)
    refine ⟨hO, ?_, ?_⟩
    · simp [BGen.sc, BGen.op, List.map_replicate, List.prod_replicate] at hop
      rw [pow_succ]
      exact hop.symm
    · intro χa χb
      have e := hval χa χb
      simp [List.map_replicate, List.prod_replicate] at e
      rw [pow_succ]
      exact e
  obtain ⟨hpO, hpop, hpval⟩ := hw t ht
  obtain ⟨haO, haop, haval⟩ := hw t.adj' hadj'
  obtain ⟨-, -, hmO, hmop, -, -, hmval, -⟩ := h1 E B (t.adj'.pw m) (t.pw m) haO hpO
  have eop : t.adj'.op = t.adj.op := rfl
  have evl : ∀ χa χb, t.adj'.val χa χb = t.val χa χb := fun _ _ => rfl
  refine ⟨hpO, hpop, hmO, ?_, ?_, rfl⟩
  · show ((t.adj'.pw m).mul (t.pw m)).op = _
    rw [hmop, haop, hpop, eop, hadjOp, star_pow, ContinuousLinearMap.star_eq_adjoint]
  · intro χa χb
    show ((t.adj'.pw m).mul (t.pw m)).val χa χb = _
    rw [hmval, haval, hpval, evl, ← pow_add, two_mul]

end PositivityTheory.Rg.BcB.F

end
