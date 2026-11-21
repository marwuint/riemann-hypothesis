import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OrthogonalFrameIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

def iotaV (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

def DictWith (Q : ∀ (g : ℕ) (lab : Fin g → D.host.E →+* ℂ)
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab) (ik : U.Comp → Fin F.n),
    (∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) → Prop) : Prop :=
  IsUnf U ∧ (∀ k, ModelW V hr (U.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U V hr dict (iotaV V hr ι) e F ik φ th x₀ ∧ Q g _ F ik φ

def IsDict : Prop := DictWith V hr U dict ι x₀ fun _ _ _ _ _ => True

def ValDict (c0 : ℂ) (xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ) (f : Rul Xo c) : Prop :=
  DictWith V hr U dict ι x₀ fun _ _ F ik φ => ∀ h γ : GA D V, MarkBy U V hr dict (iotaV V hr ι) F ik φ h γ →
    rdU U f (dict h).1 (dict h).2 = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

theorem cXiVal_iff {c : Coeff l} (σ0 : c.F →+* ℂ) {Tup : Type} (d : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ (σ0.comp ((d t).eF.symm : (d t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 d U₂ dict₂ (iotaV V hr ι) x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, ValDict V hr (U₂ t) (dict₂ t) ι x₀ c0 (xi t) (d t).cδ := Iff.rfl

end Value

end GlobalTheory.ClassTieCompare
