import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGOthNotDvd

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_inModP_Bg (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p X.B.g S y ↔ InModP X p (gOf p) S y := by
  unfold InModP
  rw [imA_span_Bg X p]

theorem imA_OEp_one (p : TypX X) : (1 : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) ∈ OEp X p :=
  ⟨1, Subring.one_mem _, map_one _⟩

theorem imA_OEp_sub (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s - t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩

abbrev epsP (p : TypX X) : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E := PI.FinKW.psiV X.B.I p.1 X.ew

theorem imA_eps_mem (p : TypX X) : epsP X p ∈ OEp X p := ⟨X.ew, X.ew_int, rfl⟩

theorem imA_eps_idem (p : TypX X) : epsP X p * epsP X p = epsP X p := by
  unfold epsP
  rw [← map_mul, X.ew_idem]

private theorem latLoc_ringOfIntegers_incl (p : TypX X) (x : 𝓞 X.B.I.E) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((1 : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  unfold latLoc at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩
    funext i
    simp [ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem latLoc_adicIntegers_incl (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u := by
    funext i
    simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c hu

theorem imA_lat_OEp (p : TypX X) {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    t • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro b hb
    unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb
    induction hb using Subring.closure_induction with
    | mem z hz =>
      intro w hw
      rcases hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · obtain ⟨x, rfl⟩ := RingHom.mem_range.mp he
        convert latLoc_ringOfIntegers_incl X p x hw using 2
        simp [PI.FinKW.psiV]
      · have hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F := hy
        convert latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2
        simp [PI.FinKW.psiV] <;> rfl
    | zero => intro w _; simp
    | one => intro w hw; simpa using hw
    | add a b _ _ ha hb => intro w hw; rw [map_add, add_smul]; exact add_mem (ha w hw) (hb w hw)
    | neg a _ ha => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (ha w hw)
    | mul a b _ _ ha hb => intro w hw; rw [map_mul, mul_smul]; exact ha _ (hb w hw)
  obtain ⟨a, ha, rfl⟩ := ht
  exact key a ha u hu

end MassDataIdxSteps
