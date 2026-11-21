import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MidDatum

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : HeightOneSpectrum (𝓞 D.host.F) :=
  HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P)

theorem isOver_vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : IsOver (vUnder (t := t) P) (seamP t.seam P) := by
  unfold IsOver vUnder
  rw [HeightOneSpectrum.under_asIdeal]

end MidDatum

end GlobalTheory.TwU

end
