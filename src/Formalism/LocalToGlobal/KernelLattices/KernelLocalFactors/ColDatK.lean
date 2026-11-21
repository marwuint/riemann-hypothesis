import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.ColumnData.GlobTied
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainOneP
import Formalism.LocalToGlobal.Columns.RefXi1Above
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)

theorem embT_ofRec : Cd.TaylorLogMetric.embT (Car.ofRec D) = TaylorLogMetric.embT D := rfl

theorem lamOf_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.lamOf (Car.ofRec D) cc δ = TaylorLogMetric.lamOf D cc δ := rfl

theorem La_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.La (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) L L' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := rfl

theorem Iop_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (G : TaylorLogMetric.VC D N N' → ℂ) :
    Cd.TaylorLogMetric.Iop (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) La₁ La₂ G = TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) La₁ La₂ G := rfl

theorem isCurveIdeal_ofRec (cc : Ideal (𝓞 D.host.K)) : Cd.TaylorLogMetric.IsCurveIdeal (Car.ofRec D) cc ↔ TaylorLogMetric.IsCurveIdeal D cc := Iff.rfl

theorem isTwelfthRootDisc_ofData_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Car.ofRec D) cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl

theorem isChi_ofRec (χ : TaylorLogMetric.IdE D → ℂ) : Cd.TaylorLogMetric.IsChi (Car.ofRec D) χ ↔ TaylorLogMetric.IsChi D χ := Iff.rfl

theorem admissible_ofData_iff {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.admitted (Car.ofRec D) N N' L L' ↔ TaylorLogMetric.admitted D N N' L L' := Iff.rfl

theorem isDgen_ofRec (cD : D.what₂.Tau → ℂ) : Cd.IsDgen (Car.ofRec D) cD ↔ IsDgen D cD := Iff.rfl

variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

def KapChoice.ofCar {γ₀ : IsoK D} (k : Cd.KapChoice (D := Car.ofRec D) γ₀) : KapChoice γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

def Base.ofCar (B : Cd.Base (Car.ofRec D) cc δ) : Base D cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := KapChoice.ofCar B.kc

theorem Base.ofCar_toCar (B : Base D cc δ) : Base.ofCar B.toCar = B := rfl

theorem Base.toCar_ofCar (B : Cd.Base (Car.ofRec D) cc δ) : (Base.ofCar B).toCar = B := rfl

theorem Base.kappa_toCar (B : Base D cc δ) : B.toCar.kappa = B.kappa := rfl

theorem Base.stdOK_toCar (B : Base D cc δ) : B.toCar.StdOK ↔ B.StdOK := Iff.rfl

theorem Base.thMM_toCar (B : Base D cc δ) : B.toCar.thMM = B.thMM := rfl

theorem Base.thMoved_toCar (B : Base D cc δ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : B.toCar.thMoved N N' L L' = B.thMoved N N' L L' := rfl

theorem chiFac_ofRec (χ : TaylorLogMetric.IdE D → ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.Base.chiFac (D := Car.ofRec D) χ N N' L L' = Base.chiFac χ N N' L L' := rfl

theorem Base.eNat_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.eNat χ = B.eNat χ := rfl

theorem Base.eqP_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.EqP χ ↔ B.EqP χ := Iff.rfl

variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

def Seam.ofCar (s : Cd.Seam (Car.ofRec D) X) : Seam D X := ⟨s.iE, s.iT, s.σ₀⟩

theorem Seam.ok_toCar (s : Seam D X) : s.toCar.Ok ↔ s.Ok := Iff.rfl

theorem ambOf_toCar (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    Cd.ambOf s.toCar B.toCar χ cD = ambOf s B χ cD := rfl

theorem ambOf_ofCar (s : Cd.Seam (Car.ofRec D) X) (B : Cd.Base (Car.ofRec D) cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf (Seam.ofCar s) (Base.ofCar B) χ cD = Cd.ambOf s B χ cD := rfl

end Bridge

section OverColDat

variable (d : ColDat)

variable {d}

theorem AmbIn.amb_sig (I : AmbIn d) : I.amb.σ₀ = d.σ₀ := rfl

theorem AmbIn.amb_cD (I : AmbIn d) : I.amb.cD = I.cD := rfl

end OverColDat

namespace Test

end Test

end Formalism.L2.Ker
