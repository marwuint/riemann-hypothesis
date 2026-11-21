import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H1MultiplicativeGroup

structure Cov (A : Type) [CommRing A] where

  B : Type
  [cr : CommRing B]
  [alg : Algebra A B]
  [et : Algebra.Etale A B]
  [ff : Module.FaithfullyFlat A B]

attribute [instance] Cov.cr Cov.alg Cov.et Cov.ff

end LateralTheory.E.H1MultiplicativeGroup
