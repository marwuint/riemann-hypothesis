import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SPack (D : D7) (F : ∀ u, Forms0 D u) where
  X : HidaSetting D
  hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I
  Y : Formalism.L2.SG.Full.Full X
  fin : FinX Y
  ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ
  measTie : X.MeasTie hb
  ψ_char : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ
  ψ_std : Formalism.L2.SG.LocVol.IsStdChar ψ
  measCompat : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ
  locCompat : ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w
  tr : ∀ u, Transport X u (F u)
  into : ∀ u, ColDictInto X (tr u) Y.hK
  bij : ∀ u, ColDictBij X (tr u) Y.hK
  lev : ∀ u, LevelMatch X (tr u) Y.hK
  isom : ∀ u, ColDictIsom X (tr u) Y.hK (Y.cs u) (fin.shInj u)
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : GoodOp X

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure SRest {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) where
  hI : SIso D.s (sOf P.fin)
  autTie : Formalism.MainNotions.S.AutTie D P.X.B P.X.pl
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    colDict P.X (P.tr u) P.Y.hK (P.into u) (P.bij u) (hI.eCu u x) = D.s_Cu u x
  j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G
  rowPin : ∀ x : D.what₂.EE, hI.eHH (D.sEE x) = conjHH P.X P.G (j x)
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

def SRest.toSTies {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : Formalism.L2.SG.SpectralTiesReal.STies D where
  X := P.X
  hb := P.hb
  Y := P.Y
  hI := fun _ => S.hI
  ψ := P.ψ
  autTie := S.autTie
  measTie := P.measTie
  ψ_char := P.ψ_char
  ψ_std := P.ψ_std
  measCompat := P.measCompat
  locCompat := P.locCompat

theorem SRest.rowTie {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : RowDictTie P.X P.G S.hI.eHH :=
  ⟨S.j, S.rowPin⟩

def SPack.toNew {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
    (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) : SNew D where
  s := sOf P.fin
  s_HH := hD
  s_Cu := fun u => colDictT P.X (P.tr u) P.Y.hK (P.fin.shInj u) (P.into u) (P.bij u)
  s_PlF := Equiv.refl _
  s_Cu_isom := fun u x y => P.isom u x y
  sEE := (conjHH P.X P.G).comp j.toLinearIsometry

end GlobalTheory.Mem.SRe

end
