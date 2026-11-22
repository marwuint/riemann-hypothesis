import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := _root_.GlobalTheory.AdjLocIt.adj_locIt D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := _root_.GlobalTheory.AdjLocIt.adj_locIt D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

end GlobalTheory.PairIt

end
