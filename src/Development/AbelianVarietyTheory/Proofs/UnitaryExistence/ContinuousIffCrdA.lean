import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspFormLaws
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)

abbrev pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
abbrev pFin : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

def crdR : V.V ≃ₗ[D.host.E] (Fin r → D.host.E) := (V.frame.reindex (finCongr hr)).equivFun

def gramR : Matrix (Fin r) (Fin r) D.host.E := (Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ

theorem herm_crdR (x y : V.V) : herm (gramR V hr) (crdR V hr x) (crdR V hr y) = V.hT y x := by
  subst hr
  rw [Formalism.L2.Herm.hT_crd D.sp.cm V]
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [crdR, gramR, finCongr_refl, Matrix.reindex_refl_refl, Module.Basis.reindex_refl]
  change _ * V.gram b a * cc _ = cc _ * V.gram b a * _
  unfold Formalism.L2.Herm.crd
  ring

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩

def spOf : ConjugateFieldNorm.HSpace D.host.E r where
  Gm := gramR V hr
  Gm_herm a b := V.herm.eq _ _
  Gm_det h := by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    refine hv ((congrArg _ (V.nondeg.2 x fun y => ?_)).trans (map_zero _))
    rw [← herm_crdR V hr, herm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, show ∑ a, crdR V hr x a * gramR V hr a b = 0 from congrFun h0 b, zero_mul]
  L := V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E))
  L_fg := V.standardTuple_isLattice.fg.map _
  L_span := by
    have := congrArg (Submodule.map (crdR V hr).toLinearMap) V.standardTuple_isLattice.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this
    exact this
  L_dual v := by
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    have h1 : crdR V hr x ∈ V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E)) ↔ x ∈ V.L0 :=
      ⟨fun ⟨y, hy, e⟩ => (crdR V hr).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, IsIntegral ℤ (V.hT y x) := by
      conv_lhs => rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_one_iff]
      rfl
    rw [h1, h2]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact (herm_crdR V hr x y).symm ▸ h y hy
    · intro h y hy
      exact herm_crdR V hr x y ▸ h _ ⟨y, hy, rfl⟩

structure IsCoord (V' : ConjugateFieldNorm.HSpace D.host.E r) (ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V) : Prop where
  sp : V' = spOf V hr
  inf : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (infHom V (ψ g)).val = g.1.1.val
  fin : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (finHom V (ψ g)).val = g.2.1.val
  top : AutomorphismGroupTopologies.topG D.host.F V' = TopologicalSpace.induced ψ inferInstance

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

theorem IsCoord.mem_GQ (h : IsCoord V hr V' ψ) (g) : ψ g ∈ GQ V ↔ g ∈ AutomorphismGroupTopologies.ratG D.host.F V' := by
  subst hr
  have h1 : (HA.mat _ _ _ (ψ g)).val.map pInf = g.1.1.val := h.inf g
  have h2 : (HA.mat _ _ _ (ψ g)).val.map pFin = g.2.1.val := h.fin g
  constructor
  · rintro ⟨γ, -, e⟩
    have e' : (HA.mat _ _ _ (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := (congrArg Units.val e).symm
    refine ⟨γ, ?_, ?_⟩
    · rw [← h1, e']; ext i j; simp [inclR, ConjugateFieldNorm.incl]
    · rw [← h2, e']; ext i j; simp [inclR, ConjugateFieldNorm.incl]
  · rintro ⟨γ, e1, e2⟩
    obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    have e' : (HA.mat _ _ _ (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := by
      ext i j
      refine e.injective (Prod.ext ?_ ?_)
      · rw [(he _).1, (he _).1]
        refine (congrFun (congrFun (h1.trans e1) i) j).trans ?_
        rfl
      · rw [(he _).2, (he _).2]
        refine (congrFun (congrFun (h2.trans e2) i) j).trans ?_
        rfl
    refine ⟨γ, ?_, Units.ext e'.symm⟩
    have hu : Formalism.UG.cT (sigR _ D.sp.cm.sig) (HA.mat _ _ _ (ψ g)).val * JR _ V.gram * (HA.mat _ _ _ (ψ g)).val =
      JR _ V.gram := (ψ g).2
    have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
    change Formalism.UG.cT _ γ.val * V.gram * γ.val = V.gram
    refine Matrix.map_injective hinj ?_
    change (_ : Matrix _ _ _).map _ = JR _ V.gram
    rw [← hu, e', Matrix.map_mul, Matrix.map_mul]
    congr 2

def IsCoord.quotEquiv (h : IsCoord V hr V' ψ) : AutomorphismGroupTopologies.AutQ D.host.F V' ≃ᵐ Formalism.L2.Pj.AutQ V where
  toEquiv := Quotient.congr ψ.toEquiv fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← h.mem_GQ, map_mul, map_inv]
    rfl
  measurable_toFun s hs := by
    change MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (ψ ⁻¹' (Formalism.L2.Pj.autMk V ⁻¹' s))
    rw [h.top, borel_comap]
    exact ⟨_, hs, rfl⟩
  measurable_invFun s hs := by
    have hs' : MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s) := hs
    rw [h.top, borel_comap] at hs'
    obtain ⟨t, ht, e⟩ := hs'
    change MeasurableSet (ψ.symm ⁻¹' (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s))
    rw [← e, ← Set.preimage_comp]
    simpa using ht

theorem IsCoord.quotEquiv_mk (h : IsCoord V hr V' ψ) (g) :
    h.quotEquiv (AutomorphismGroupTopologies.autMk D.host.F V' g) = Formalism.L2.Pj.autMk V (ψ g) := rfl

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

end Rec

end GlobalTheory.CoreLawsCompare
