import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralHeckeElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMulRight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PartDims

section Lin

theorem finrank_comap {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V U : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) (hU : U ≤ V) : Module.finrank ℂ (U.comap M.e) = Module.finrank ℂ U ∧ FiniteDimensional ℂ U := by
  have e : U.comap M.e ≃ₗ[ℂ] U :=
    (Submodule.equivMapOfInjective M.e h.1 (U.comap M.e)).trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_self (h.2.1.symm ▸ hU)))
  exact ⟨e.finrank_eq, e.finiteDimensional⟩

theorem homInto_comp {H H' S X : Type} [Group H] [Group H'] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ H S) (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃* H') :
    homInto σ (ρ.comp Φ.toMonoidHom : Representation ℂ H X) C =
      homInto (σ.comp Φ.symm.toMonoidHom : Representation ℂ H' S) ρ C := by
  ext f
  refine and_congr_right fun _ => ⟨fun h g s => ?_, fun h g s => ?_⟩
  · have := h (Φ.symm g) s
    simpa using this
  · have := h (Φ g) s
    simpa using this

end Lin

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

theorem mem_levi_flag_of_mem_parabolic (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) :
    κ ∈ levG V β (withP L P) ∧ levChi V β (withP L P) κ = 1 ∧ levChi V β (flag1L L) κ = 1 := by
  have h1 : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  refine ⟨⟨hκ.1, hκ.2.1, ?_⟩, ?_, ?_⟩
  · show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · rw [levChi_withP hs hQ, h1, blockDiagonalExtendByOnePrimeField_one]; rfl
  · have h := levChi_flag (β := β) hs hQ κ
    unfold levChi at h ⊢
    rw [levFn_flag1, h]

theorem mult_le {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  refine Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => ?_, hT.equiv, hT.cont⟩
  rw [← (h k hk).2]
  exact hT.lev v k (h k hk).1 g

theorem goodPart_le_flag {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) e ≤
      goodPart θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) e :=
  inf_le_inf_right _ (mult_le θ M fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
    exact ⟨h1, h2.trans h3.symm⟩)

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

theorem gaL_star (hs : L.s = 0) (hQ : L.Q = ∅) (hc : ∀ g, star (c g) = c g) (φ : GA D V → ℂ) :
    gaL V β L eG c (star φ) = star (gaL V β L eG c φ) := by
  funext h
  have h1 : ∀ g, actG0 V β L (eG g) (star φ) h = star (actG0 V β L (eG g) φ h) := by
    intro g
    unfold actG0
    split_ifs with hk
    · simp [levChi_flag hs hQ]
    · simp
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Pi.star_apply, star_sum,
    smul_eq_mul, star_mul', hc]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (h1 g)

variable {eG c} {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → ℂ[X]}
  {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X}

theorem fixed_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg))
    {k : GfC V} (hk : (k : GA D V) ∈ levG V β (flag1L L)) : ρ k x = x := by
  obtain ⟨h1, h2, -⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
  have := mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, h1, rfl⟩))
  simpa [h2, sub_eq_zero] using this

theorem isTopologicalGroup_GA (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem isOpen_stab (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  first
  | (rename_i h_5 h_6 h_16 h_17; revert D V β L G h_5 h_6 eG c P Pl0 ok pl q Sg X h_16 h_17 ρ hs hQ x hx; exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser)
  | exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | (apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser ..)

theorem isGoodRep_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L)
    (h : killed ρ (eqSet V β L eG c P ok pl q Sg) ≠ ⊥) : IsGoodRep V β L eG c ρ := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  choose κ hκ using fun g => hl (eG g)
  refine ⟨x, h0, fun k hk => fixed_of_killed hs hQ hx hk, fun g => ⟨κ g, (hκ g).1⟩, hκ, ?_⟩
  have := mem_killed.1 hx _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))
  simpa [sub_eq_zero, map_sum, LinearMap.sum_apply] using this

end Level

section Hecke

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {Pl0 : Type} {ok : Set Pl0}
  {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

theorem mem_hPart {Sg : Pl0 → ℂ[X]} {x : MMap M} : x ∈ hPart M J ok pl q Sg ↔
    ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V (pl P) k α → Bridge.IsDC J α⁻¹ R →
      heckeOn M R x = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • x := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  exact ⟨fun h P hP k hk α R ha hR => h P hP k hk α ha R hR, fun h P hP k hk α ha R hR => h P hP k hk α R ha hR⟩

theorem exists_conjModel {S' : D.what₂.Tau → SPar} (h : ∀ τ, S' τ = dualPar (S τ)) (M : DSModel V S) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ),
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  obtain rfl : S' = fun τ => dualPar (S τ) := funext h
  exact _root_.GlobalTheory.ConjDS.exists_conjModel M

end Hecke

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem rank_zeroth_component_eq : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
  simp [Ranks.rankY]

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem star_levChi (b : Bool) {κ : GA D (Yc D 0)} (hκ : κ ∈ levS _ (R.βY 0) (R.dat0 (R.levR F b))) :
    levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL)) κ = star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) κ) := by
  have hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (R.levR F b).H := hκ.2.2
  have h1 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) κ
  have h2 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) κ
  replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
  replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
  refine h1.trans (Eq.trans ?_ (congrArg star h2).symm)
  have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
    exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
  have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
    have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
  rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
  rfl

end GlobalTheory.PartDims

end
