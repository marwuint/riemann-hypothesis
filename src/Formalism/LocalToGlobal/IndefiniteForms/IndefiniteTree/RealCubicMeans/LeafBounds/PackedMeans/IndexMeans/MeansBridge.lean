import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.OnObjOf3XEq
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.LeafMeansFree
import Development.WeilBound.SupplementaryPages.FaceFrameMatrix
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansPf

noncomputable section

open NumberField IsDedekindDomain Finset
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.IndefR.Obj

namespace IxMeans

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RecTie (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) {Tau : Type} [Fintype Tau] (P : MeansPack Tau (J.ι j)) : Prop where
  hX : J.X j = P.X
  hsl : J.sl j = P.sl
  hT : (faceLiftFactor R F I J hd j).T = (P.T : ℝ)
  hLL : (faceLiftPage R F I J hd).LL0 = P.LL0
  hU : (faceLiftFactor R F I J hd j).U = P.U
  hE : J.E0 j = P.E0
  hcc : J.cc j = P.cc
  hQ : J.Qcc j = P.Qcc

end IxMeans
