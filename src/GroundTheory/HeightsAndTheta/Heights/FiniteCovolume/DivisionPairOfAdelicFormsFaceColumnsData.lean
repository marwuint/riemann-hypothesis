import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsClosedUnitaryOfComplex

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder Pointwise

noncomputable section

set_option linter.unusedSectionVars false

theorem unitaryGroupMatrix_eq_unitaryOf {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : A →+* A) (H : Matrix ι ι A) :
    unitaryGroupMatrix s H = IndefiniteRowSideFullHecke.FiniteCovolume.unitaryOf s Hᵀ := by
  ext g
  rw [mem_unitaryGroupMatrix]
  change _ ↔ (g : Matrix ι ι A)ᵀ * Hᵀ * (g : Matrix ι ι A).map s = Hᵀ
  constructor
  · intro hg
    have := congrArg Matrix.transpose hg
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro hg
    have := congrArg Matrix.transpose hg
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

def subgroupHomeo {G : Type*} [Group G] [TopologicalSpace G] {S T : Subgroup G} (e : S = T) :
    S ≃ₜ T :=
  Homeomorph.setCongr (congrArg SetLike.coe e)

theorem subgroupHomeo_apply {G : Type*} [Group G] [TopologicalSpace G] {S T : Subgroup G}
    (e : S = T) (x : S) : subgroupHomeo e x = MulEquiv.subgroupCongr e x := rfl

section HidaSetting

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

variable [IsCMField E]

theorem conjHom_eq_conjE : conjHom F E = IndefiniteRowSideFullHecke.FiniteCovolume.conjE E := by
  ext x
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [IndefiniteRowSideFullHecke.FiniteCovolume.conjE_apply, IsCMField.complexEmbedding_complexConj]
  exact embedding_conj w.embedding x

theorem fDeg.equiv : finrank ℚ F = IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E :=
  (CMExtension.equivMaximalRealSubfield F E).toRatAlgEquiv.toLinearEquiv.finrank_eq

variable {W : Type*} [AddCommGroup W] [Module E W] {N : ℕ}

def divisionPairOfAdelicFormsFaceColumnsData (h : HermitianForm F E W) (v : Basis (Fin N) E W) :
    IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N where
  J := (gram h.toSesq v)ᵀ
  herm := by
    rw [Matrix.transpose_transpose, Matrix.transpose_map, ← conjHom_eq_conjE (F := F)]
    exact (isHermitianFor_gram h v).symm
  nondeg := by
    rw [Matrix.det_transpose]
    exact isUnit_det_gram h v

theorem matrixHermSpace_gram (h : HermitianForm F E W) (v : Basis (Fin N) E W) :
    (divisionPairOfAdelicFormsFaceColumnsData h v).J = (gram h.toSesq v)ᵀ := rfl

theorem HermSpace.h.equiv (h : HermitianForm F E W) (v : Basis (Fin N) E W) (x y : W) :
    (divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun x) (v.equivFun y) = h.toSesq y x := by
  rw [sesq_eq_sum h.toSesq v y x, Finset.sum_comm]
  simp only [IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, matrixHermSpace_gram,
    Matrix.transpose_apply, Basis.equivFun_apply, ← conjHom_eq_conjE (F := F)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (conjHom F E) ((v.repr y) j) * _ * _
  ring

variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

theorem unitaryGroup.equiv :
    unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) =
      IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup (divisionPairOfAdelicFormsFaceColumnsData h v) := by
  rw [unitaryGroupMatrix_eq_unitaryOf, conjHom_eq_conjE]
  rfl

def unitaryEquiv : h.unitaryGroup ≃* IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  (unitaryGroupEquivMatrix h v).trans (MulEquiv.subgroupCongr (unitaryGroup.equiv h v))

theorem unitaryEquiv_coe (g : h.unitaryGroup) :
    (unitaryEquiv h v g : GL (Fin N) E) = (unitaryGroupEquivMatrix h v g : GL (Fin N) E) :=
  MulEquiv.subgroupCongr_apply (unitaryGroup.equiv h v) _

theorem unitaryEquiv_apply (g : h.unitaryGroup) :
    ((unitaryEquiv h v g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W) :=
  unitaryGroupEquivMatrix_apply h v g

theorem unitaryEquiv_mulVec (g : h.unitaryGroup) (x : W) :
    ((unitaryEquiv h v g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v.equivFun x =
      v.equivFun ((g : W ≃ₗ[E] W) x) := by
  rw [unitaryEquiv_apply]
  simp only [Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr v v _ x

theorem archUnitary.equiv : archUnitary h v = IndefiniteRowSideFullHecke.FiniteCovolume.realPoints (divisionPairOfAdelicFormsFaceColumnsData h v) := by
  unfold archUnitary IndefiniteRowSideFullHecke.FiniteCovolume.realPoints
  congr 1
  funext w
  rw [unitaryGroupMatrix_eq_unitaryOf]
  congr 1

def realEquiv : archUnitary h v ≃* IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v) :=
  MulEquiv.subgroupCongr (archUnitary.equiv h v)

@[simp]
theorem coe_realEquiv (g : archUnitary h v) :
    ((realEquiv h v g : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) :
      InfinitePlace E → GL (Fin N) ℂ) = g :=
  MulEquiv.subgroupCongr_apply _ g

omit [IsCMField E] in
theorem archEmbed_apply (γ : h.unitaryGroup) (w : InfinitePlace E) :
    ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL (Fin N) ℂ) w =
      Matrix.GeneralLinearGroup.map w.embedding (unitaryGroupEquivMatrix h v γ : GL (Fin N) E) :=
  rfl

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in
theorem toReal_apply (V : IndefiniteRowSideFullHecke.FiniteCovolume.HermSpace E N)
    (g : IndefiniteRowSideFullHecke.FiniteCovolume.unitaryGroup V) (w : InfinitePlace E) :
    ((IndefiniteRowSideFullHecke.FiniteCovolume.toReal V g : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts V) :
      InfinitePlace E → GL (Fin N) ℂ) w = Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) :=
  rfl

theorem archEmbed.equiv (γ : h.unitaryGroup) :
    realEquiv h v (archEmbed h v γ) = IndefiniteRowSideFullHecke.FiniteCovolume.toReal (divisionPairOfAdelicFormsFaceColumnsData h v) (unitaryEquiv h v γ) :=
  by
    apply Subtype.ext
    rw [coe_realEquiv]
    funext w
    rw [archEmbed_apply, toReal_apply, unitaryEquiv_coe]

theorem archEmbed_comp :
    (realEquiv h v).toMonoidHom.comp (archEmbed h v) =
      (IndefiniteRowSideFullHecke.FiniteCovolume.toReal (divisionPairOfAdelicFormsFaceColumnsData h v)).comp (unitaryEquiv h v).toMonoidHom :=
  MonoidHom.ext (archEmbed.equiv h v)

omit [NumberField E] [IsTotallyComplex E] [IsCMField E] in

theorem vecAt.equiv (x : W) : vecAt v x = IndefiniteRowSideFullHecke.FiniteCovolume.realVec (v.equivFun x) := rfl

theorem invApply.equiv (g : archUnitary h v) (y : InfinitePlace E → Fin N → ℂ) :
    invApply g y = IndefiniteRowSideFullHecke.FiniteCovolume.gAct (realEquiv h v g)⁻¹ y := rfl

variable {h v}

variable (v) in

def latOf (L : Submodule (𝓞 E) (Fin N → E)) : AddSubgroup W :=
  L.toAddSubgroup.comap (v.equivFun : W →+ (Fin N → E))

theorem mem_latOf {L : Submodule (𝓞 E) (Fin N → E)} {x : W} :
    x ∈ latOf v L ↔ v.equivFun x ∈ L := Iff.rfl

theorem latOf_injective : Function.Injective (latOf (W := W) v) := by
  intro L L' hLL
  ext y
  have := SetLike.ext_iff.mp hLL (v.equivFun.symm y)
  rwa [mem_latOf, mem_latOf, LinearEquiv.apply_symm_apply] at this

theorem exists_latOf {La : AddSubgroup W} (hLa : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) :
    ∃ L : Submodule (𝓞 E) (Fin N → E), latOf v L = La := by
  refine ⟨{ carrier := {y | v.equivFun.symm y ∈ La}
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_ofPred_eq, map_add] at *
              exact La.add_mem ha hb
            zero_mem' := by simp
            smul_mem' := fun c y hy => by
              simp only [Set.mem_ofPred_eq] at *
              rw [← IsScalarTower.algebraMap_smul E c y, map_smul]
              exact hLa c _ hy }, ?_⟩
  ext x
  change v.equivFun.symm (v.equivFun x) ∈ La ↔ x ∈ La
  rw [LinearEquiv.symm_apply_apply]

theorem coe_latOf (L : Submodule (𝓞 E) (Fin N → E)) :
    (latOf v L : Set W) = v.equivFun.symm '' (L : Set (Fin N → E)) := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_latOf]
  constructor
  · intro hx
    exact ⟨_, hx, v.equivFun.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]

theorem latOf_eq_map (L : Submodule (𝓞 E) (Fin N → E)) :
    latOf v L = ((L.restrictScalars ℤ).map
      (((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) : (Fin N → E) →ₗ[E] W).restrictScalars ℤ)).toAddSubgroup := by
  apply SetLike.coe_injective
  rw [coe_latOf, Submodule.coe_toAddSubgroup, Submodule.map_coe]
  rfl

theorem IsLattice.equiv :
    (∀ L : Submodule (𝓞 E) (Fin N → E),
      FiniteCovolume.IsLattice E (latOf v L) ↔ IndefiniteRowSideFullHecke.FiniteCovolume.IsLattice L) ∧
    ∀ La : AddSubgroup W, FiniteCovolume.IsLattice E La →
      ∃ L : Submodule (𝓞 E) (Fin N → E), latOf v L = La := by
  refine ⟨fun L => ?_, fun La hLa => exists_latOf hLa.smul_mem⟩
  have hfg : (latOf v L).FG ↔ L.FG := by
    rw [latOf_eq_map, ← Submodule.fg_iff_addSubgroup_fg]
    exact (Submodule.fg_map_iff ((((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) :
      (Fin N → E) →ₗ[E] W).restrictScalars ℤ)) (fun a b hab => v.equivFun.symm.injective hab)).trans
      (Submodule.FG.restrictScalars_iff (R := ℤ) (A := 𝓞 E) (S := L))
  have hspan : Submodule.span E (latOf v L : Set W) = ⊤ ↔
      Submodule.span E (L : Set (Fin N → E)) = ⊤ := by
    rw [coe_latOf]
    change Submodule.span E (((v.equivFun.symm : (Fin N → E) ≃ₗ[E] W) : (Fin N → E) →ₗ[E] W) ''
      (L : Set (Fin N → E))) = ⊤ ↔ _
    rw [Submodule.span_image, Submodule.map_eq_top_iff]
  have hsmul : ∀ (a : 𝓞 E) (x : W), x ∈ latOf v L → (a : E) • x ∈ latOf v L := by
    intro a x hx
    rw [mem_latOf, map_smul]
    exact L.smul_mem a hx
  constructor
  · intro hL
    exact ⟨hfg.1 hL.fg, hspan.1 hL.span_eq_top⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hsmul, hfg.2 h1, hspan.2 h2⟩

theorem isIntegral_conj_iff (a : E) :
    IsIntegral ℤ (conjHom F E a) ↔ IsIntegral ℤ a := by
  constructor
  · intro ha
    have := ha.map (conjHom F E).toIntAlgHom
    simpa [conj_conj] using this
  · intro ha
    exact ha.map (conjHom F E).toIntAlgHom

theorem dual.equiv (L : Submodule (𝓞 E) (Fin N → E)) :
    latOf v (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L) = dualLattice h (latOf v L) := by
  ext y
  change (∀ x ∈ L, IsIntegral ℤ ((divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun y) x)) ↔
    ∀ x ∈ latOf v L, h.toSesq y x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have := hy _ (mem_latOf.mp hx)
    rw [HermSpace.h.equiv, ← h.isSymm.eq y x, isIntegral_conj_iff] at this
    exact this
  · intro hy x hx
    have := hy (v.equivFun.symm x) (by rwa [mem_latOf, LinearEquiv.apply_symm_apply])
    rw [← v.equivFun.apply_symm_apply x, HermSpace.h.equiv, ← h.isSymm.eq, isIntegral_conj_iff]
    exact this

theorem unitary_smul (γ : h.unitaryGroup) (x : W) : γ • x = (γ : W ≃ₗ[E] W) x := rfl

theorem smul_latOf (γ : h.unitaryGroup) (L : Submodule (𝓞 E) (Fin N → E)) :
    γ • latOf v L = latOf v (IndefiniteRowSideFullHecke.FiniteCovolume.act (unitaryEquiv h v γ : GL (Fin N) E) L) := by
  ext x
  change x ∈ ((γ : h.unitaryGroup) : W ≃ₗ[E] W) • latOf v L ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem,
    show ((γ : W ≃ₗ[E] W))⁻¹ • x = γ⁻¹ • x from rfl, mem_latOf, mem_latOf]
  change _ ↔ v.equivFun x ∈ L.map (IndefiniteRowSideFullHecke.FiniteCovolume.linO (unitaryEquiv h v γ : GL (Fin N) E))
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ _ = _
    rw [unitaryEquiv_mulVec, ← unitary_smul, smul_inv_smul]
  · rintro ⟨z, hz, hzx⟩
    change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ z = _ at hzx
    rw [← v.equivFun.apply_symm_apply z, unitaryEquiv_mulVec, ← unitary_smul] at hzx
    have := v.equivFun.injective hzx
    rw [← this, inv_smul_smul, LinearEquiv.apply_symm_apply]
    exact hz

theorem latticeStab.equiv (L : Submodule (𝓞 E) (Fin N → E)) (γ : h.unitaryGroup) :
    γ ∈ latticeStab h (latOf v L) ↔ unitaryEquiv h v γ ∈ IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L := by
  rw [latticeStab, MulAction.mem_stabilizer_iff, smul_latOf]
  exact latOf_injective.eq_iff

theorem vecStabGroup.equiv (L : Submodule (𝓞 E) (Fin N → E)) (x : W) :
    (vecStabGroup h v (latOf v L) x).map (realEquiv h v).toMonoidHom =
      IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x) := by
  have hK : (MulAction.stabilizer (latticeStab h (latOf v L)) x).map (latticeStab h (latOf v L)).subtype =
      (IndefiniteRowSideFullHecke.FiniteCovolume.stab (divisionPairOfAdelicFormsFaceColumnsData h v) L ⊓
        IndefiniteRowSideFullHecke.FiniteCovolume.fixVec (divisionPairOfAdelicFormsFaceColumnsData h v) (v.equivFun x)).comap (unitaryEquiv h v).toMonoidHom := by
    ext γ
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨(latticeStab.equiv L _).1 δ.2, ?_⟩
      change ((unitaryEquiv h v (δ : h.unitaryGroup) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ
        v.equivFun x = v.equivFun x
      rw [unitaryEquiv_mulVec]
      exact congrArg v.equivFun hδ
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, (latticeStab.equiv L γ).2 h1⟩, ?_, rfl⟩
      change ((unitaryEquiv h v γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ
        v.equivFun x = v.equivFun x at h2
      rw [unitaryEquiv_mulVec] at h2
      exact v.equivFun.injective h2
  unfold vecStabGroup IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf
  rw [← Subgroup.map_map, hK, Subgroup.map_map, archEmbed_comp, ← Subgroup.map_map,
    Subgroup.map_comap_eq_self_of_surjective (unitaryEquiv h v).surjective]

end HidaSetting

universe u w

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
