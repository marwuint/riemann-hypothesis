import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

variable (k d) in

@[ext] structure COSub where

  sub : AddSubgroup (Fin d → k)
  isOpen : IsOpen (sub : Set (Fin d → k))
  isCompact : IsCompact (sub : Set (Fin d → k))

def gHom (g : GL (Fin d) k) : (Fin d → k) →+ (Fin d → k) :=
  (Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) k)).toAddMonoidHom

def COSub.act (L : COSub k d) (g : GL (Fin d) k) : COSub k d where
  sub := L.sub.comap (gHom g⁻¹)
  isOpen := L.isOpen.preimage (glHomeo g).symm.continuous
  isCompact := (glHomeo g).symm.isCompact_preimage.2 L.isCompact

theorem COSub.mem_act {L : COSub k d} {g : GL (Fin d) k} {y : Fin d → k} :
    y ∈ (L.act g).sub ↔ ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y ∈ L.sub := Iff.rfl

theorem isClopen_coset (L : COSub k d) (c : Fin d → k) : IsClopen {y | y - c ∈ L.sub} :=
  ⟨L.isCompact.isClosed.preimage (continuous_id.sub continuous_const),
    L.isOpen.preimage (continuous_id.sub continuous_const)⟩

open Classical in

def ind (L : COSub k d) (c : Fin d → k) (a : V) : SchF k d V :=
  ⟨fun y => if y - c ∈ L.sub then a else 0, by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
    · by_cases hx : x - c ∈ L.sub
      · filter_upwards [(isClopen_coset L c).isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∈ L.sub := hy
        rw [if_pos hx, if_pos hy']
      · filter_upwards [(isClopen_coset L c).compl.isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∉ L.sub := hy
        rw [if_neg hx, if_neg hy']
    · refine HasCompactSupport.intro (L.isCompact.image (continuous_add_right c)) fun x hx => ?_
      rw [if_neg]
      intro h
      exact hx ⟨x - c, h, by simp⟩⟩

open Classical in
theorem ind_apply (L : COSub k d) (c y : Fin d → k) (a : V) :
    (ind L c a).1 y = if y - c ∈ L.sub then a else 0 := rfl

end GlobalTheory.CompanionTheory.BZCore

end
