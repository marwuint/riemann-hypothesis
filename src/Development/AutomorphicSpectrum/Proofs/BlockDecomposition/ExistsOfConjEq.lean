import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeFrameEmbedding

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Formalism.UG Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Group

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S} {P : Matrix n m S}

def uHom (h : IsFrame c J K a V P) : UJ c K →* UJ c J where
  toFun g := ⟨Units.map (embHom h.pv) g.1, frame_embedding_unitary h g.2⟩
  map_one' := Subtype.ext (map_one (Units.map (embHom h.pv)))
  map_mul' g g' := Subtype.ext (map_mul (Units.map (embHom h.pv)) g.1 g'.1)

end Group

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
