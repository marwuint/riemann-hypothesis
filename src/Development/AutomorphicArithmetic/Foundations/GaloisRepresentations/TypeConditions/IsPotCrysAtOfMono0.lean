import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.WeilBound.CoreStatements.AutomorphicKernels.TemperedUnitNorm.NormEqOneOfTemperedRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal

noncomputable section

namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Gw {w : PlE H} (y : A.LP w) : Prop := A.unr y ∨ (thr w (A.lpDim y) = 2 ∧ Sep N A y)

variable {N A}
theorem Gw.nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Gw N A y) : Nc N A y :=
  h.elim Nc.of_unr fun k => nc_of_sep T k.1 k.2
end

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem NcW.congr {x y : WD h} (k : NcW x) (d : y.lpDim = x.lpDim) (m : x.mono0 → y.mono0)
    (e : ∀ σ ∈ Ine (F := E) B, y.inePol σ = x.inePol σ) : NcW y :=
  ⟨fun σ hσ => by rw [e σ (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), d]; exact k.1 σ hσ, m k.2.1,
    fun γ hγ hc z hz => k.2.2 γ hγ hc z (by rwa [← e γ hγ, ← d])⟩

theorem NcW.char {x c : WD h} (k : NcW x) (hc : c.lpDim = 1) (hu : c.unr) : NcW (x.lpChar c) := by
  refine k.congr ?_ (WD.monomial_char_iff _ _ hc).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨n', b, rfl⟩ := c.exists_rep
    rw [WD.lpDim_mk] at hc
    rw [WD.lpChar_mk, WD.lpDim_mk, WD.lpDim_mk, Module.finrank_tensorProduct, hc, mul_one]
  · rw [GlobalTheory.RowTieLP.inePol_char hc hσ (z := 1) (by rw [inePol_of_unr hu hσ, hc]; simp), scaleRoots_one]

theorem NcW.tw {x : WD h} (k : NcW x) (s : ℝ) : NcW (x.lpTw s) := by
  refine k.congr ?_ (WD.monomial_twist_iff _ _).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.lpDim_mk, WD.lpDim_mk]
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ,
      deg_ineIncl]
    simp
end
end UpperTheory.GalS

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

def _root_.UpperTheory.GalS.IsGaloisRepOfN (D : D7) {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (UpperTheory.GalS.Gw D.nd D.naut (D.naut.locG π w) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.unr (D.naut.locG π w) →
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

structure IsAttachedAwayS : Prop where
  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))
  ss : IsSSRep r
  away : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    UpperTheory.GalS.Aw (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r)
      (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)))
  temp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((a : ℝ) + 3) / 2)

structure IsAttachedHodgeS : Prop extends IsAttachedAwayS D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
    (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsDeRhamOf D ι π s r Bw) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)) ∧
      (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w))

def _root_.UpperTheory.GalS.GalHodge0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedHodgeS D T ι π s r

def _root_.UpperTheory.GalS.GalHodgeN : Prop :=
  UpperTheory.GalS.GalHodge0 D T ∧ GlobalTheory.TypeLeaf.WildOne D ∧
  (∀ π : D.naut.CG D.R.r, D.naut.csd π → ∀ w w', IsConjPl D.host w w' →
    UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w')) ∧
  ∀ (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host), (S.e1 π).1.TameAt w →
    UpperTheory.GalS.Tm D.nd D.naut (D.naut.locG π w)

variable {D T ι π s r}

theorem IsAttachedAwayS.frob (h : IsAttachedAwayS D T ι π s r) {w : PlE D.host}
    (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (hu : D.naut.unr (D.naut.locG π w)) :
    (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))).map fun α => X - C α).prod := by
  have h1 := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
  have e := (h.away w hl).eq_unr ((T.unr w _).1 h1)
  have h2 : (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r).unr := by rw [e, ← T.unr]; exact h1
  refine ⟨(GlobalTheory.WeilDeligne.unr_wdOf_iff hl ι h.cont).1 h2, fun B σ hB hσ => ?_⟩
  rw [GlobalTheory.WeilDeligne.frobEig_wdOf hl ι h.cont h2 hB hσ, e, T.frobEig w _ h1]

end GlobalTheory.TripleLocal

namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

def _root_.UpperTheory.GalS.GaloisRepsN (D : D7) : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, UpperTheory.GalS.IsGaloisRepOfN D π l ι r

end GlobalTheory.HodgeOfTrue

namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
