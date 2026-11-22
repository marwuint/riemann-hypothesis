import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FrameCoefficientData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.NonGenericCompare

section Place
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [StarRing E]
variable (o : Type) [CommRing o] [Algebra o F] [Algebra o E]

structure SamePlace (L : LocE F E) : Prop where
  int_iff : ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x
  star_eq : ∀ x : E, star x = L.cj x

variable {o}

theorem SamePlace.mem_O [IsScalarTower o F E] {L : LocE F E} (h : SamePlace o L) (x : E) :
    x ∈ MaxOrd o E ↔ x ∈ L.O := by
  rw [L.O_def, mem_integralClosure_iff]
  letI : Algebra o 𝒪[F] :=
    ((algebraMap o F).codRestrict 𝒪[F] fun a => (h.int_iff _).2 ⟨a, rfl⟩).toAlgebra
  haveI : IsScalarTower o 𝒪[F] E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply o F E]; rfl
  haveI : Algebra.IsIntegral o 𝒪[F] := ⟨fun y => by
    obtain ⟨a, ha⟩ := (h.int_iff y).1 y.2
    have : y = algebraMap o 𝒪[F] a := Subtype.ext ha.symm
    rw [this]; exact isIntegral_algebraMap⟩
  exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans x hx⟩

end Place

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [StarRing E]
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Algebra o F]
  [IsFractionRing o F] [Algebra o E] [IsScalarTower o F E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure Match (P : LocNG.FPair H r) (D : Data o F E V r) : Prop where
  place : SamePlace o M.L
  h_eq : ∀ x y, D.h x y = H.h x y
  ψ_eq : ∀ x, (D.ψ x : ℂ) = M.L.psi0 x
  θ_eq : D.θ = LocNG.theta M
  f_eq : D.A.f = P.A.f
  f'_eq : D.B.f = P.B.f
  y_eq : D.A.y = P.A.es
  y'_eq : D.B.y = P.B.es
  T_eq : D.A.T = P.A.T
  T'_eq : D.B.T = P.B.T

namespace Match
variable {P : LocNG.FPair H r} {D : Data o F E V r} {S : Frames M.L r k}
variable (m : Match P D) (c : Coord P S)

def lat (Λ : Submodule (MaxOrd o E) V) : Submodule M.L.O S.V where
  carrier := {y | c.e.symm y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simpa only [Set.mem_setOf_eq, map_add] using Λ.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun s a ha => by
    have := Λ.smul_mem ⟨s, (m.place.mem_O _).2 s.2⟩ ha
    change c.e.symm ((s : E) • a) ∈ Λ
    rw [map_smul]; exact this

include m

end Match

end GlobalTheory.NonGenericCompare
