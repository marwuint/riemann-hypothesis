import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def QFam.pinTup (F : QFam v t) (sc cT : ℕ → ℂ) : VTup t where
  Q := Finset.univ.image fun i => (F.Q i).q.v
  sc := sc
  eQ := fun j => if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0
  eQT := fun j h => aconv (List.ofFn fun i => (F.Q i).eT j h)
  dQ := fun j α γ => if j < D.R.m then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0
  ε := fun j α => if (∃ ρ, j + 2 * ρ + 2 = D.R.m) ∨ j = 0 then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) else 0
  εT := fun n _ β => Finsupp.single 1 (∏ i, (F.Q i).wt n (F.eqv n β i))
  FX := fun _ _ => Set.univ
  FY := fun j => {f | ∀ i, (F.Q i).Typed j f}
  FT := Set.univ
  cQ := fun j => ∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹
  cT := cT

end GlobalTheory.QPl

namespace GlobalTheory.Fam

end GlobalTheory.Fam

end
