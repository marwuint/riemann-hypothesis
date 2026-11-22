import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.FiniteLevel

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cmap_disc (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) = ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h
      ext x
      exact h (f x) ⟨x, rfl⟩ (show x ∈ f ⁻¹' {f x} from rfl)
  rw [hset]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete {y}).preimage f.continuous).isCompact (isOpen_discrete _)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

abbrev CG (M : TRep R G) : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)

instance CG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (CG M).V := by
  have : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V := ‹DiscreteTopology M.V›
  have := cmap_disc G (M.resSub (⊥ : Subgroup G)).V
  exact (IsEmbedding.subtypeVal (p := fun f => f ∈ coindSub (⊥ : Subgroup G) (M.resSub ⊥))).discreteTopology

def iCG (M : TRep R G) : M.V →ₗ[R] (CG M).V where
  toFun m := ⟨⟨fun x => M.rho x m, M.cont.comp (f := fun x : G => (x, m)) (continuous_id.prodMk continuous_const)⟩,
    fun x g => by
      show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
      rw [map_mul, Module.End.mul_apply]⟩
  map_add' a b := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (a + b) = M.rho x a + M.rho x b; simp)
  map_smul' r a := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (r • a) = r • M.rho x a; simp)

@[simp] theorem iCG_apply (M : TRep R G) (m : M.V) (x : G) : (iCG M m).1 x = M.rho x m := rfl

theorem iCG_equiv (M : TRep R G) (g : G) (m : M.V) : iCG M (M.rho g m) = (CG M).rho g (iCG M m) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  show M.rho x (M.rho g m) = M.rho (x * g) m
  rw [map_mul, Module.End.mul_apply]

def QG (M : TRep R G) : TRep R G where
  V := (CG M).V ⧸ LinearMap.range (iCG M)
  rho := (CG M).rho.quotient (LinearMap.range (iCG M)) (fun g x hx => by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨M.rho g m, iCG_equiv M g m⟩)
  cont := by
    have hq : IsQuotientMap (fun p : G × (CG M).V => (p.1, (LinearMap.range (iCG M)).mkQ p.2)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ _)).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    exact (Submodule.isQuotientMap_mkQ _).continuous.comp (CG M).cont

instance QG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (QG M).V := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  exact (Submodule.isQuotientMap_mkQ (LinearMap.range (iCG M))).isOpen_preimage.1 (isOpen_discrete _)

def pLin (M : TRep R G) : (CG M).V →ₗ[R] (QG M).V := (LinearMap.range (iCG M)).mkQ

end InflationIsomorphism

end

end ReciprocityTheory.Coh
