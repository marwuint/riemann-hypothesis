import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.SigThreeSetFiniteOverField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

def LGUnr3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l), Continuous ρ → V.IsRi π (VData.toRecRep ρ) →
    ∀ M : ℕ, (V.spec K 3).level π M → ∀ v : HeightOneSpectrum (𝓞 K), ((M : ℕ) : 𝓞 K) ∉ v.asIdeal →
    ((l : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ (A : ValuationSubring QbarQ) (σ : K.fixingSubgroup),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := K) A v →
    Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) (IntermediateField.fixingSubgroupEquiv K σ) →
    ((ρ σ⁻¹ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec K 3).hecke π v

def LGUnr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Formalism.ConjugateSelfDual.Irred W → V.IsRi π W → ∀ M : ℕ, (V.spec ℚ 2).level π M → ∀ v : HeightOneSpectrum (𝓞 ℚ),
    ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → Formalism.ConjugateSelfDual.UnramAt W v ∧
    ∀ (A : ValuationSubring QbarQ) (σ : GQ),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := ℚ) A v → Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A (Formalism.ConjugateSelfDual.normV v) σ →
    ((W σ⁻¹ : GL (Fin 2) (QbarL l)) : Matrix (Fin 2) (Fin 2) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec ℚ 2).hecke π v

def LocGlobWt2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W → ∀ e : ℕ,
    V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) →
    (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]

def RhoDet3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (π : (V.spec K 3).Rep)
    (ρ ρ' : K.fixingSubgroup →* GL (Fin 3) (QbarL l)), Continuous ρ → Continuous ρ' →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ') →
    V.IsRi π (VData.toRecRep ρ) → V.IsRi π (VData.toRecRep ρ') → IsIsoRep ρ ρ'

def RhoDet2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W W' : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' → V.IsRi π W → V.IsRi π W' → IsIsoRep W W'

def HeckeInt3 : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (M e : ℕ), 1 ≤ e → ∀ π ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e, ∀ v : HeightOneSpectrum (𝓞 K),
    ((M : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ z ∈ ((V.spec K 3).hecke π v).roots,
    IsIntegral ℤ ((Formalism.ConjugateSelfDual.normV v : ℂ) ^ (e - 1) * z)

def HeckeInt2 : Prop :=
  ∀ (M e : ℕ), ∀ π ∈ Sig2 V M e, ∀ v : HeightOneSpectrum (𝓞 ℚ), ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
    ∀ z ∈ ((V.spec ℚ 2).hecke π v).roots, IsIntegral ℤ z

def LocGlob2G : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (ι : QbarL l ≃+* ℂ) (W : GQ →* GL (Fin 2) (QbarL l)),
    Continuous W → ∀ j : ℤ, IsRiAt V ι π (twistRep W ((epsL l) ^ j)) → ∀ M : ℕ, 0 < M → Ram2 V l W M →
    (V.spec ℚ 2).level π M

def CAut (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  ∀ (π : (V.spec F n).Rep) (σ : ℂ ≃+* ℂ), ∃ π' : (V.spec F n).Rep,
    (∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
      (V.spec F n).hecke π' v = ((V.spec F n).hecke π v).map σ.toRingHom) ∧
    (∀ τ : F →+* ℂ, (V.spec F n).wt π' (σ.toRingHom.comp τ) = (V.spec F n).wt π τ) ∧
    (V.IsRACSDC F n π → V.IsRACSDC F n π')

def ClozelAutR : Prop :=
  (∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    CAut V K 3) ∧ CAut V ℚ 2

structure Inp : Prop where
  lg3Pt : LG.LocGlob3Pt V
  lg2G : LocGlob2G V
  clozelR : ClozelAutR V
  lgUnr3 : LGUnr3 V
  lgUnr2 : LGUnr2 V
  wt2 : LocGlobWt2 V
  det3 : RhoDet3 V
  det2 : RhoDet2 V
  int3 : HeckeInt3 V
  int2 : HeckeInt2 V
  deJong : Formalism.MainNotions.UnitaryThreeHeightBounds.DeJong D V

structure Dat (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] (g1 : GQ) : Prop where
  data : UnitaryThreeData V l e χ K
  norm : IsNormElt V l e χ K g1
  a : UnitaryThreeFiniteness V l e χ K g1
  b : UnitaryThreeIrreduciblePoints V l e χ K g1

end Formalism.MainNotions.V.Pf.V3
