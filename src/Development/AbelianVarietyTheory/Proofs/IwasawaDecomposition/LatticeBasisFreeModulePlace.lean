import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFix

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem charpoly_eq_prod_of_iSup_eigenspace {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (s : Finset K)
    (h : ⨆ r ∈ s, f.eigenspace r = ⊤) :
    ∃ m : Multiset K, f.charpoly = (m.map fun a => X - C a).prod := by
  classical
  let E : s → Submodule K V := fun r => f.eigenspace (r : K)
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep f).comp Subtype.val_injective
  have htop : iSup E = ⊤ := by
    rw [← h, iSup_subtype]
  have hint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).mpr ⟨hind, htop⟩
  let bE : ∀ r : s, Module.Basis (Module.Free.ChooseBasisIndex K (E r)) K (E r) :=
    fun r => Module.Free.chooseBasis K (E r)
  let bb := hint.collectedBasis bE
  have hdiag : LinearMap.toMatrix bb bb f = Matrix.diagonal (fun x => ((x.1 : s) : K)) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    have hy : (bb y : V) = (bE y.1 y.2 : V) := by
      rw [hint.collectedBasis_coe]
    have hev : f (bE y.1 y.2 : V) = ((y.1 : s) : K) • (bE y.1 y.2 : V) :=
      Module.End.mem_eigenspace_iff.mp (bE y.1 y.2).2
    rw [hy, hev, ← hy, map_smul, bb.repr_self, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hxy), if_neg hxy, smul_zero]
  refine ⟨Finset.univ.val.map (fun x : (Σ r : s, Module.Free.ChooseBasisIndex K (E r)) => ((x.1 : s) : K)), ?_⟩
  rw [← LinearMap.charpoly_toMatrix f bb, hdiag, Matrix.charpoly_diagonal, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  rfl

theorem charpoly_restrict_map_eq_prod {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) [Module.Free O B] [Module.Finite O B] (f : Module.End (FractionRing O) V)
    (hf : ∀ x ∈ B, f x ∈ B) (s : Finset (FractionRing O))
    (hs : ∀ x ∈ B, x ∈ ⨆ r ∈ s, f.eigenspace r) :
    ∃ m : Multiset (FractionRing O), (LinearMap.charpoly ((f.restrictScalars O).restrict hf)).map
      (algebraMap O (FractionRing O)) = (m.map fun a => X - C a).prod := by
  classical
  let b := Module.Free.chooseBasis O B
  let v : Module.Free.ChooseBasisIndex O B → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  let V' := Submodule.span (FractionRing O) (Set.range v)
  have hBV : ∀ x ∈ B, x ∈ V' := by
    intro x hx
    have h1 : (⟨x, hx⟩ : B) ∈ Submodule.span O (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := B.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O (FractionRing O) _ h2
  have hV' : ∀ x ∈ V', f x ∈ V' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => f x ∈ V') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact hBV _ (hf _ (b i).2)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact V'.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact V'.smul_mem a hx
  let f' := f.restrict hV'
  let bK : Module.Basis (Module.Free.ChooseBasisIndex O B) (FractionRing O) V' := Module.Basis.span hli
  haveI : FiniteDimensional (FractionRing O) V' := Module.Finite.of_basis bK
  set g := (f.restrictScalars O).restrict hf with hgdef
  have hmat : LinearMap.toMatrix bK bK f' = (LinearMap.toMatrix b b g).map (algebraMap O (FractionRing O)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hg : (g (b j) : V) = ∑ i, b.repr (g (b j)) i • v i := by
      calc (g (b j) : V) = ((∑ i, b.repr (g (b j)) i • b i : B) : V) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (g (b j)) i • v i := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    have hf' : f' (bK j) = ∑ i, algebraMap O (FractionRing O) (b.repr (g (b j)) i) • bK i := by
      have hbK : ∀ i, (bK i : V) = v i := fun i => by rw [Module.Basis.span_apply]
      apply Subtype.ext
      simp only [f', LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul]
      simp_rw [hbK]
      rw [show f (v j) = (g (b j) : V) from rfl, hg]
      simp [algebraMap_smul]
    rw [hf', bK.repr_sum_self]
  have hcp : (LinearMap.charpoly g).map (algebraMap O (FractionRing O)) = f'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map, ← hmat, LinearMap.charpoly_toMatrix]
  rw [hcp]
  apply charpoly_eq_prod_of_iSup_eigenspace f' s
  have hle : V' ≤ LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) := by
    rw [GlobalTheory.JointDiag.ker_prod, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hs _ (b i).2
  rw [← GlobalTheory.JointDiag.ker_prod, LinearMap.ker_eq_top]
  ext y
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, GlobalTheory.JointDiag.aeval_restrict_coe]
  exact hle y.2

end GlobalTheory.HeightCounting.FormsStep

namespace GlobalTheory.HeightCounting.FormsStep

end GlobalTheory.HeightCounting.FormsStep
