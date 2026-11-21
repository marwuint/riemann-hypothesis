import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.TopFrame

theorem sumE_one_single {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) (t : Eˣ) (r b : Fin N) :
    GlobalTheory.TopStep.sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = N then (t : E) else 1) else 0 := by
  rcases GlobalTheory.TopStep.idx_cases hN r with ⟨i, rfl⟩ | rfl
  · have h := congrFun (GlobalTheory.TopStep.prH_sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1)) i
    refine h.trans ?_
    show (Pi.single b (1 : E) : Fin N → E) (Formalism.L2.Col.Br.iC hN i) = _
    have hi : ¬ (Formalism.L2.Col.Br.iC hN i).val + 1 = N := by
      show ¬ i.val + 1 = N
      have := i.2
      omega
    rw [if_neg hi, Pi.single_apply]
    simp only [Fin.ext_iff]
  · have hi : (Formalism.L2.Col.Br.iL hN).val + 1 = N := by
      show n + 1 = N
      omega
    rw [GlobalTheory.TopStep.sumE_last, if_pos hi, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> simp

theorem frsF_top {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (hI : I.Ok) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (j : ℕ) (hj : j = B.R.m) (β : Ch₀ j) (r b : Fin (B.R.N j)) :
    Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := by
  subst hj
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hPr := (base_fields_primes_ok B X).2.1
  have hπ := GlobalTheory.Mem.Col2.PerLaw.piT_notMem_Q hI u a
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have h2 := h1.fr ⟨P.1, hQ⟩ r b
  have h3 := (hA.base _ le_rfl β).1.fr ⟨P.1, hSQ⟩ r b
  have h4 := (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective (h3.symm.trans h2)
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩, h4, tilF_fr I.sel (I.tup a) hPr u hπ]
  refine (sumE_one_single _ _ r b).trans ?_
  rw [unitOf_val (hπ ⟨P.1, hQ⟩)]

end GlobalTheory.Fam.TopFrame
