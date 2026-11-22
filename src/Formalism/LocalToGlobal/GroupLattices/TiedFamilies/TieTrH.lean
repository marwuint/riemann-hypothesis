import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev setGat : D7 := { D with gat := g', gat_d := hd' }

open Formalism.L2.Herm

structure FullTiedNoG (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

def FullTiedNoG.toFull {D : D7} (X : FullTiedNoG D) (g : GTied D X.base) : FullTied D := { X with g := g }

def hermSet (H : HermTied D) : HermTied (setGat D g' hd') := { H with }

set_option maxHeartbeats 4000000 in

def atTSet {u : D.what₂.Word}
    {e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)} (A : AtT D u e eF) :
    AtT (setGat D g' hd') u e eF := { A with }

set_option maxHeartbeats 4000000 in
def allSet (H : AllTied D) : AllTied (setGat D g' hd') where
  base := hermSet D g' hd' H.base
  atT := fun u => atTSet D g' hd' (H.atT u)
  vol := H.vol

end Formalism.L2.G
