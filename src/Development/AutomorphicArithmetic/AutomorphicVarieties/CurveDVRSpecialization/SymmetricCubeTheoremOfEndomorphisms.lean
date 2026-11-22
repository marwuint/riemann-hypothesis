import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RestrictionToDecompositionGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UniversalDiagonalOfTriangularPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H

private theorem tri_of_char {O G A : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Group G]
    [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra O A] (h2 : IsUnit (2 : O))
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O A a = 0) {η : G →* ℤˣ} {Ψ : G →* Oˣ} {c g₁ : G} (hM : Marks η Ψ c g₁)
    {r : G →* GG 3 A} (hr : UnitaryThreeInertia.Red η Ψ r) (hN : Normalised c g₁ r) (U : Subgroup G) (hU : U.FiniteIndex)
    (hch : ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly) :
    Upper η r ∨ Lower η r := by
  letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift _ (algebraMap O A) h0).toAlgebra
  let Φ : G →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ
  have e : ∀ g, ((r0 η Φ g).mat).map (algebraMap (ResidueField O) A) = ((r0 η Ψ g).mat).map (algebraMap O A) := by
    intro g
    rw [GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, tor_val, tor_val, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [show Φ g ^ wt1 i = Units.map (residue O).toMonoidHom (Ψ g ^ wt1 i) from
      (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) _).symm]
    rfl
  refine (constOfChar G (ResidueField O) A ?_ η Φ c g₁ ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩ r hr.mult
    (fun g => ?_) hN U hU fun g hg hη => ?_).1
  · simpa [map_ofNat] using (h2.map (residue O)).ne_zero
  · show Units.map _ (Ψ c) = 1
    rw [hM.Ψc, map_one]
  · have := hM.Ψg.map (residue O)
    rwa [map_sub, map_pow, map_one] at this
  · rw [e]; exact hr.red g
  · rw [e]; exact hch g hg hη

