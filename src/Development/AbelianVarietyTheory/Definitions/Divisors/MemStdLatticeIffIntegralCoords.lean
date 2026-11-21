import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame GlobalTheory.StdFrame
open scoped TensorProduct Matrix

namespace GlobalTheory.StdFrameModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.StdFrame.instCMHostS

variable {D : D7}

theorem hostF_eq (D : D7) : D.host.F = maximalRealSubfield D.host.E := rfl

abbrev sw (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* ReciprocityTheory.Aut.AL D.host.E := tensCastR (hostF_eq D)

theorem sw_tmul (a : Af D.host.F) (x : D.host.E) : sw D (a ⊗ₜ x) = x ⊗ₜ a := rfl

theorem sw_symm_tmul (a : Af D.host.F) (x : D.host.E) : (sw D).symm (x ⊗ₜ a) = a ⊗ₜ x := rfl

theorem sw_sig (y : ReciprocityTheory.Aut.AL D.host.E) :
    (sw D).symm (ReciprocityTheory.Aut.conjAL D.host.E y) = sigR (Af D.host.F) D.sp.cm.sig ((sw D).symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingEquiv.map_zero, RingHom.map_zero]
  | tmul x a => rfl
  | add x y hx hy => rw [RingHom.map_add, RingEquiv.map_add, RingEquiv.map_add, RingHom.map_add, hx, hy]

theorem mem_GA_iff {V : HSp D} (hg : V.gram = 1) (κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) :
    κ ∈ ReciprocityTheory.Aut.GA D.host.E V.rank ↔
      Formalism.UG.bc (sw D).symm.toRingHom κ ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have h1 : JR (F := D.host.F) (Af D.host.F) V.gram = 1 := by
    rw [hg, JR]; exact Matrix.map_one _ (map_zero _) (map_one _)
  change κ.1 * ReciprocityTheory.Aut.conjT _ κ.1 = 1 ↔
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) * JR (F := D.host.F) (Af D.host.F) V.gram *
      κ.1.map (sw D).symm.toRingHom = JR (F := D.host.F) (Af D.host.F) V.gram
  have h2 : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) κ.1).map (sw D).symm.toRingHom := by
    ext i j
    exact (sw_sig _).symm
  rw [h1, Matrix.mul_one, h2, ← Matrix.map_mul, mul_eq_one_comm,
    ← Matrix.map_one (sw D).symm.toRingHom (map_zero _) (map_one _)]
  exact ⟨fun h => by rw [h], fun h => Matrix.map_injective (sw D).symm.injective h⟩

theorem exists_lift {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    ∃ g : GA D V, infHom V g = 1 ∧ finHom V g = Formalism.UG.bc (sw D).symm.toRingHom κ.1 :=
  GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) ((mem_GA_iff hg κ.1).1 κ.2)

def unitPsi {V : HSp D} (hg : V.gram = 1) : RowPsi V V.rank where
  ψ := MonoidHom.mk' (fun κ => (exists_lift hg κ).choose) fun a b => by
    refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
    · rw [map_mul, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, mul_one]
    · rw [map_mul, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2,
        ← map_mul]
      rfl
  inj := fun a b h => by
    have h1 := congrArg (finHom V) h
    simp only [MonoidHom.mk'_apply] at h1
    rw [(exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2] at h1
    exact Subtype.ext (Units.ext (Matrix.map_injective (sw D).symm.injective (congrArg Units.val h1)))
  into := fun κ => (exists_lift hg κ).choose_spec.1
  onto := fun g hgf => by
    have e : Formalism.UG.bc (sw D).symm.toRingHom (Formalism.UG.bc (sw D).toRingHom (finHom V g)) = finHom V g := by
      ext i j
      exact (sw D).symm_apply_apply _
    refine ⟨⟨Formalism.UG.bc (sw D).toRingHom (finHom V g), (mem_GA_iff hg _).2 (by
      rw [e]; exact GlobalTheory.UnitarySplit.finHom_mem V g)⟩, GlobalTheory.UnitarySplit.ga_ext V ?_ ?_⟩
    · exact (exists_lift hg _).choose_spec.1.trans (Eq.symm hgf)
    · exact (exists_lift hg _).choose_spec.2.trans e

theorem finMat_unitPsi {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    finMat D.sp.cm.sig V.gram ((unitPsi hg).ψ κ) = κ.1.1.map (sw D).symm :=
  congrArg Units.val (exists_lift hg κ).choose_spec.2

theorem mem_std_lattice_iff_integral_coords {V : HSp D} (h : OrthFrame V) (x : Fin V.rank → D.host.E) :
    x ∈ L0c D V ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := h.mem_iff x

theorem tmul_mem (o : 𝓞 D.host.E) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    sw D (a ⊗ₜ (o : D.host.E)) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  have e : sw D (a ⊗ₜ (o : D.host.E)) =
      ((o : D.host.E) ⊗ₜ (1 : Af D.host.F) : ReciprocityTheory.Aut.AL D.host.E) * ((1 : D.host.E) ⊗ₜ a) := by
    rw [sw_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨o, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩))

theorem int_of_mem {V : HSp D} (h : OrthFrame V) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) (i : Fin V.rank) : sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((mem_std_lattice_iff_integral_coords h x).1 hx i)
    have := tmul_mem o ha
    rw [show (o : D.host.E) = x i from ho] at this
    exact this
  | zero => rw [Pi.zero_apply, RingEquiv.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Pi.add_apply, RingEquiv.map_add]; exact add_mem hy hz
  | neg y _ hy => rw [Pi.neg_apply, RingEquiv.map_neg]; exact neg_mem hy

theorem smul_gen {M : ℕ} (L : Set (Fin M → D.host.E)) (c : Af D.host.F ⊗[D.host.F] D.host.E)
    (hc : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, c • (fun i => a ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E L)
    {w : Fin M → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latHat D.host.F D.host.E L) :
    c • w ∈ latHat D.host.F D.host.E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem smul_closure {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (e : B →+* A) (S : AddSubgroup (Fin M → A)) (T : Set B)
    (h : ∀ t ∈ T, ∀ w ∈ S, e t • w ∈ S) {r : B} (hr : r ∈ Subring.closure T) : ∀ w ∈ S, e r • w ∈ S := by
  induction hr using Subring.closure_induction with
  | mem r hr => exact h r hr
  | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [map_one, one_smul]
  | add x y _ _ hx hy => intro w hw; rw [map_add, add_smul]; exact add_mem (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [map_mul, mul_smul]; exact hx _ (hy w hw)

theorem smul_mem {V : HSp D} (h : OrthFrame V) {r : ReciprocityTheory.Aut.AL D.host.E} (hr : r ∈ ReciprocityTheory.Aut.ALint D.host.E) :
    ∀ w ∈ latHat D.host.F D.host.E (L0c D V), (sw D).symm r • w ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine smul_closure (sw D).symm.toRingHom _ _ (fun r hr w hw => ?_) hr
  rcases hr with ⟨o, rfl⟩ | ⟨b, hb, rfl⟩
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, (o : D.host.E) • x, ?_, ?_⟩) hw
    · rw [mem_std_lattice_iff_integral_coords h] at hx ⊢
      exact fun i => Submodule.smul_mem _ o (hx i)
    · funext i
      change ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => ?_, x, hx, ?_⟩) hw
    · rw [map_mul]
      exact mul_mem (hb v) (ha v)
    · funext i
      change ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]
  exact one_mem _

theorem single_mem {V : HSp D} (h : OrthFrame V) (j : Fin V.rank) :
    (Pi.single j 1 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine AddSubgroup.subset_closure ⟨1, one_mem_intAf _, Pi.single j 1, ?_, ?_⟩
  · rw [mem_std_lattice_iff_integral_coords h]
    intro a
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  · funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero]

theorem mem_latHat_iff {V : HSp D} (h : OrthFrame V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  refine ⟨int_of_mem h, fun hy => ?_⟩
  rw [pi_eq_sum_univ' y]
  refine sum_mem fun i _ => ?_
  have := smul_mem h (hy i) _ (single_mem h i)
  rw [RingEquiv.symm_apply_apply] at this
  exact this

theorem mulVec_mem {V : HSp D} (h : OrthFrame V) {κ : Formalism.AUTREP.GAf D.host.E V.rank}
    (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) :
    (κ.1.1.map (sw D).symm.toRingHom) *ᵥ y ∈ latHat D.host.F D.host.E (L0c D V) := by
  rw [mem_latHat_iff h] at hy ⊢
  intro i
  change (sw D).toRingHom (∑ j, (sw D).symm (κ.1.1 i j) * y j) ∈ _
  rw [map_sum (sw D).toRingHom]
  refine sum_mem fun j _ => ?_
  change sw D _ ∈ _
  rw [RingEquiv.map_mul, RingEquiv.apply_symm_apply]
  exact mul_mem (hκ i j) (hy j)

theorem stdPsi_unitPsi {V : HSp D} (h : OrthFrame V) : StdPsi (hostF_eq D) (unitPsi h.gram_eq) := by
  refine ⟨⟨1, 1, mul_one _, mul_one _, fun κ => ?_⟩, fun κ => ⟨fun hκ => ⟨(unitPsi h.gram_eq).into κ, fun y => ?_, by simp⟩, ?_⟩⟩
  · rw [finMat_unitPsi, Matrix.one_mul, Matrix.mul_one]
  · rw [finMat_unitPsi]
    refine ⟨mulVec_mem h hκ, fun hy => ?_⟩
    have := mulVec_mem h (inv_mem hκ) hy
    erw [Matrix.mulVec_mulVec, ← Matrix.map_mul] at this
    rw [show (κ⁻¹).1.1 * κ.1.1 = 1 from Units.inv_mul κ.1, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mulVec] at this
    exact this
  · rintro ⟨-, hk, -⟩ i j
    have := (mem_latHat_iff h _).1 ((hk _).1 (single_mem h j)) i
    rw [finMat_unitPsi, Matrix.mulVec_single_one] at this
    change sw D ((sw D).symm (κ.1.1 i j)) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

end GlobalTheory.StdFrameModel

end
