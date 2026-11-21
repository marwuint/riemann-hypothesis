import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
