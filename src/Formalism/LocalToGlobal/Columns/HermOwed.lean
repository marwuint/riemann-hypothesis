import Formalism.LocalToGlobal.Columns.ValuationPosIffMemSeen
import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Formalism.LocalToGlobal.Columns.RecLevelLocT

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

structure AtTOwed (hS : SpStd d.toColBase) (hH : HostHyp d) where
  disc : ∀ u, AtTDisc (d.colRec a) u
  moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)
  xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)

def hermAtT (hS : SpStd d.toColBase) (hH : HostHyp d) (O : AtTOwed a hS hH) (u : d.what₂.Word) :
    CH.AtT (d.colRec a) u (tieEV d.sp.cm d.hX d.hPr u) (fun v => tieFv d.sp.cm d.hX d.hPr u v) :=
  atTOf (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) (fun v => tieFv d.sp.cm d.hX d.hPr u v)
    (fun v x => tieFv_mk d.sp.cm d.hX d.hPr u v x) (th_seen a hH u) (O.disc u) (O.moves u) (O.xp u)

end Formalism.L2.Col
