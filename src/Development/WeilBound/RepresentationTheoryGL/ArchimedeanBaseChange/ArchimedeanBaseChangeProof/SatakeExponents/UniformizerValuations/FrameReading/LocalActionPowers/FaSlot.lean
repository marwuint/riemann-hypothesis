import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Sl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)}

def cpH (a b : ℕ) : ∀ i : Slot S, Hf E a b →* GLw a i.pl × GLw b i.pl
  | .inl w => GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1
  | .inr w => (GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1).comp (thP E a b)

def eH (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => (thP E a b).comp ((locGL E a w.1).prodMap (locGL E b w.1))

theorem atH_loc_self (w : Pl E) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b w ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

theorem atH_loc_ne {w v : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

theorem atH_thP_loc_ne {w v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v (thP E a b ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) = 1 := by
  have := GlobalTheory.CompanionTheory.SuppFinTw.atH_thP_congr (a := a) (b := b) (u := v) rfl
    (g := ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) (h := 1) (by rw [atH_loc_ne h, map_one])
  rw [this, map_one, map_one]

theorem cpH_eH_self (hS : IsSection S) (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : cpH a b i (eH a b i m) = m := by
  rcases i with w | w
  · exact atH_loc_self w.1 m
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans (atH_loc_self w.1 m)

theorem cpH_eH_ne (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (h : j ≠ i) :
    cpH a b j (eH a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact atH_loc_ne (fun e => h (congrArg Sum.inl (Subtype.ext e))) m
  · exact atH_thP_loc_ne (w := w.1) (v := v.1)
      (fun e => GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (e ▸ w.2)) m
  · refine atH_thP_loc_ne (w := w.1) (v := v.1) (fun e => ?_) m
    have e' : v.1 = GlobalTheory.EulerTw.cPl E w.1 := by rw [← e, GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (e' ▸ v.2)
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b v.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans
      (atH_loc_ne (fun e => h (congrArg Sum.inr (Subtype.ext e))) m)

end PositivityTheory.Rg.BcB.F.FA.Sl

end
