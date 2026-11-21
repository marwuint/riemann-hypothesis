import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToP

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this

end GlobalTheory.StdAtPrime
