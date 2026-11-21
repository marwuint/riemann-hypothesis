import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.ThetaLiftIndependence.Statement
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.DivisionValues Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace GSD

variable (S : GSD K)

theorem wt_eq (h : S.Ok) (s : S.Sec) (c : S.Cl) :
    (S.toCSDOf h s).wt c = Nat.card (MulAction.stabilizer S.G (s.rep c)) := by
  unfold CSD.wt
  exact Fintype.card_eq_nat_card

theorem card_stab_smul (g : S.G) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (g • d)) = Nat.card (MulAction.stabilizer S.G d) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * (x : S.G) * g, ?_⟩
      invFun := fun y => ⟨g * (y : S.G) * g⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp x.2, inv_smul_smul]
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.mp y.2]
  · exact Subtype.ext (by simp [mul_assoc])
  · exact Subtype.ext (by simp [mul_assoc])

theorem ipOf_eq_sum (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = letI := h.fintypeCl
      ∑ c : S.Cl, ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : K))⁻¹ * S.pair (φ (s.rep c)) (ψ (s.rep c)) := by
  unfold ipOf CSD.csum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [S.wt_eq h s c]

theorem mem_intOf_iff (N : S.D → Submodule (𝓞 K) S.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K))) (s : S.Sec)
    (φ : S.EqFun) : φ ∈ S.intOf N ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ N (s.rep c) := by
  constructor
  · intro hφ c
    exact hφ (s.rep c)
  · intro hφ d
    have e := s.mv_smul d
    rw [← e, φ.2, hN]
    exact Submodule.mem_map_of_mem (hφ (S.cls d))

theorem mem_intNab_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intNab ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Nab (s.rep c) := by
  exact S.mem_intOf_iff S.Nab h.nab_smul s φ

theorem mem_intDel_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Del (s.rep c) := by
  exact S.mem_intOf_iff S.Del h.del_smul s φ

def coordOf (h : S.Ok) (s : S.Sec) : S.EqFun ≃ₗ[K] (Fin (S.toCSDOf h s).dim → K) :=
  (S.resOf h s).trans (S.toCSDOf h s).basis.equivFun

theorem I_coordOf (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    (S.toCSDOf h s).I (S.coordOf h s φ) = fun c => (φ : S.D → S.V) (s.rep c) := by
  show (((S.toCSDOf h s).basis.equivFun.symm ((S.toCSDOf h s).basis.equivFun (S.resOf h s φ)) :
    (S.toCSDOf h s).Forms) : S.Cl → S.V) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem coordOf_mem_nabLat (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    S.coordOf h s φ ∈ (S.toCSDOf h s).nabLat ↔ φ ∈ S.intNab := by
  unfold CSD.nabLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intNab_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩

theorem coordOf_mem_delLat (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    S.coordOf h s φ ∈ (S.toCSDOf h s).delLat ↔ φ ∈ S.intDel := by
  unfold CSD.delLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intDel_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩

theorem map_intNab (h : S.Ok) (s : S.Sec) :
    S.intNab.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).nabLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_nabLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_nabLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp

theorem map_intDel (h : S.Ok) (s : S.Sec) :
    S.intDel.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).delLat := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hx
    exact (S.coordOf_mem_delLat h s φ).mpr hφ
  · intro hx
    refine Submodule.mem_map.mpr ⟨(S.coordOf h s).symm x, ?_, ?_⟩
    · rw [← S.coordOf_mem_delLat h s, LinearEquiv.apply_symm_apply]
      exact hx
    · simp

theorem finiteDimensional_EqFun (h : S.Ok) : FiniteDimensional K S.EqFun := by
  letI := h.fintypeCl
  haveI : Module.Finite K S.V := Module.Finite.of_basis S.bV
  exact LinearEquiv.finiteDimensional (S.resOf h S.outSec).symm

variable {S} in
theorem Sec.exists_smul (s s' : S.Sec) (c : S.Cl) : ∃ g : S.G, g • s.rep c = s'.rep c := by
  exact (S.cls_eq_iff _ _).mp ((s'.spec c).trans (s.spec c).symm)

theorem ipOf_indep (h : S.Ok) (s s' : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ipOf h s' φ ψ := by
  rw [S.ipOf_eq_sum h s, S.ipOf_eq_sum h s']
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [← hg, φ.2, ψ.2, h.inv, card_stab_smul]

def chgSec (h : S.Ok) (s s' : S.Sec) : (S.toCSDOf h s).Forms ≃ₗ[K] (S.toCSDOf h s').Forms :=
  (S.resOf h s).symm.trans (S.resOf h s')

end GSD

namespace ClsKer

variable {S S' : GSD K} (A : ClsKer S S')

theorem term_smul (φ : S.EqFun) (g : S.G) (d : S.D) (d' : S'.D) :
    A.k (g • d) d' ((φ : S.D → S.V) (g • d)) = A.k d d' ((φ : S.D → S.V) d) := by
  have e1 : ∀ y, S.ρ g⁻¹ (S.ρ g y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h1 := A.equiv g 1 d d'
  rw [one_smul, map_one] at h1
  rw [h1, φ.2]
  simp only [LinearMap.comp_apply, Module.End.one_apply, e1]

theorem resOf_opOf (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) :
    (S'.resOf h' s' (A.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((S.toCSDOf h s).wt c : K))⁻¹) (A.atReps s s') (S.resOf h s φ).1 := rfl

end ClsKer

namespace GSD

variable (S : GSD K)

def Free : Prop := ∀ (d : S.D) (g : S.G), g • d = d → g = 1

theorem forms_eq_top (h : S.Ok) (s : S.Sec) (hf : S.Free) : (S.toCSDOf h s).Forms = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  intro c γ
  have hγ : ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) = 1 :=
    hf _ _ (MulAction.mem_stabilizer_iff.mp γ.2)
  show S.ρ ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) (f c) = f c
  rw [hγ, map_one, Module.End.one_apply]

def resFree (h : S.Ok) (s : S.Sec) (hf : S.Free) : S.EqFun ≃ₗ[K] (S.Cl → S.V) :=
  (S.resOf h s).trans (LinearEquiv.ofTop _ (S.forms_eq_top h s hf))

theorem resFree_apply (h : S.Ok) (s : S.Sec) (hf : S.Free) (φ : S.EqFun) (c : S.Cl) :
    S.resFree h s hf φ c = (φ : S.D → S.V) (s.rep c) := rfl

end GSD

namespace GSD.Iso

variable {S S' : GSD K} (e : GSD.Iso S S')

theorem symm_smul (g' : S'.G) (d' : S'.D) : e.eD.symm (g' • d') = e.eG.symm g' • e.eD.symm d' := by
  rw [Equiv.symm_apply_eq, e.smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem onCl_cls (d : S.D) : e.onCl (S.cls d) = S'.cls (e.eD d) := rfl

def stabEquiv (d : S.D) : MulAction.stabilizer S.G d ≃ MulAction.stabilizer S'.G (e.eD d) :=
  Equiv.subtypeEquiv e.eG.toEquiv fun g => by
    show g ∈ MulAction.stabilizer S.G d ↔ e.eG g ∈ MulAction.stabilizer S'.G (e.eD d)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← e.smul, e.eD.apply_eq_iff_eq]

theorem card_stab (d : S.D) :
    Nat.card (MulAction.stabilizer S'.G (e.eD d)) = Nat.card (MulAction.stabilizer S.G d) := by
  exact Nat.card_congr (e.stabEquiv d).symm

theorem iso_integral_structure_equivariant (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hN : ∀ (g : S.G) (d : S.D), N (g • d) = (N d).map ((S.ρ g).restrictScalars (𝓞 K)))
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)))
    (g' : S'.G) (d' : S'.D) : N' (g' • d') = (N' d').map ((S'.ρ g').restrictScalars (𝓞 K)) := by
  obtain ⟨d, rfl⟩ := e.eD.surjective d'
  obtain ⟨g, rfl⟩ := e.eG.surjective g'
  rw [← e.smul, hc, hc, hN, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  exact e.rho g x

theorem iso_onForms_mem_integral_iff (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (φ : S.EqFun) :
    e.onForms φ ∈ S'.intOf N' ↔ φ ∈ S.intOf N := by
  constructor
  · intro hφ d
    have h1 : e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD d))) ∈ N' (e.eD d) := hφ (e.eD d)
    rw [Equiv.symm_apply_apply, hc] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    have hy' : y = (φ : S.D → S.V) d := e.eV.injective hxy
    rw [← hy']
    exact hy
  · intro hφ d'
    show e.eV ((φ : S.D → S.V) (e.eD.symm d')) ∈ N' d'
    have h2 := hc (e.eD.symm d')
    rw [Equiv.apply_symm_apply] at h2
    rw [h2]
    exact Submodule.mem_map_of_mem (hφ _)

theorem mem_intNab (φ : S.EqFun) : e.onForms φ ∈ S'.intNab ↔ φ ∈ S.intNab := by
  exact e.iso_onForms_mem_integral_iff S.Nab S'.Nab e.nab φ

theorem mem_intDel (φ : S.EqFun) : e.onForms φ ∈ S'.intDel ↔ φ ∈ S.intDel := by
  exact e.iso_onForms_mem_integral_iff S.Del S'.Del e.del φ

def mapSec (s : S.Sec) : S'.Sec where
  rep := fun c' => e.eD (s.rep (e.onCl.symm c'))
  spec := by
    intro c'
    rw [← e.onCl_cls, s.spec, Equiv.apply_symm_apply]

theorem ipOf_onForms (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ ψ : S.EqFun) :
    S'.ipOf h' s' (e.onForms φ) (e.onForms ψ) = S.ipOf h s φ ψ := by
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  rw [S'.ipOf_indep h' s' (e.mapSec s), GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Fintype.sum_equiv e.onCl.symm _ _ fun c' => ?_
  show ((Nat.card (MulAction.stabilizer S'.G (e.eD (s.rep (e.onCl.symm c')))) : K))⁻¹ *
    S'.pair (e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c'))))))
      (e.eV ((ψ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c')))))) = _
  rw [e.card_stab, Equiv.symm_apply_apply, e.pair]

include e in
theorem dim_eq (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (S'.toCSDOf h' s').dim = (S.toCSDOf h s).dim := by
  unfold CSD.dim
  exact (((S'.resOf h' s').symm.trans e.onForms.symm).trans (S.resOf h s)).finrank_eq

def coord (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (Fin (S.toCSDOf h s).dim → K) ≃ₗ[K] (Fin (S'.toCSDOf h' s').dim → K) :=
  ((S.coordOf h s).symm.trans e.onForms).trans (S'.coordOf h' s')

def refl (S : GSD K) : GSD.Iso S S where
  eG := MulEquiv.refl _
  eD := Equiv.refl _
  eV := LinearEquiv.refl _ _
  smul := fun _ _ => rfl
  rho := fun _ _ => rfl
  pair := fun _ _ => rfl
  nab := fun d => (Submodule.map_id (S.Nab d)).symm
  del := fun d => (Submodule.map_id (S.Del d)).symm
  rat := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rat_symm := by
    intro i j
    show S.bV.repr (S.bV j) i ∈ cmMax K
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem transpose_form_mul_involution (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (d' : S'.D) :
    N (e.eD.symm d') = (N' d').map ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)) := by
  have h2 := hc (e.eD.symm d')
  rw [Equiv.apply_symm_apply] at h2
  have hid : ((e.eV.symm : S'.V →ₗ[K] S.V).restrictScalars (𝓞 K)).comp
      ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K)) = LinearMap.id := by
    ext x
    simp
  rw [h2, ← Submodule.map_comp, hid, Submodule.map_id]

def symm : GSD.Iso S' S where
  eG := e.eG.symm
  eD := e.eD.symm
  eV := e.eV.symm
  smul := e.symm_smul
  rho := by
    intro g' x'
    rw [LinearEquiv.symm_apply_eq, e.rho, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  pair := by
    intro x' y'
    rw [← e.pair, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  nab := e.transpose_form_mul_involution S.Nab S'.Nab e.nab
  del := e.transpose_form_mul_involution S.Del S'.Del e.del
  rat := e.rat_symm
  rat_symm := e.rat

theorem rat_comp {ι ι' ι'' V V' V'' : Type} [Fintype ι'] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] [AddCommGroup V''] [Module K V''] (b : Basis ι K V) (b' : Basis ι' K V') (b'' : Basis ι'' K V'')
    (f : V →ₗ[K] V') (f' : V' →ₗ[K] V'') (F : Subfield K) (h : ∀ i j, b'.repr (f (b j)) i ∈ F)
    (h' : ∀ i j, b''.repr (f' (b' j)) i ∈ F) (i : ι'') (j : ι) : b''.repr (f' (f (b j))) i ∈ F := by
  rw [← b'.sum_repr (f (b j))]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun k _ => mul_mem (h k j) (h' i k)

def trans {S'' : GSD K} (e' : GSD.Iso S' S'') : GSD.Iso S S'' where
  eG := e.eG.trans e'.eG
  eD := e.eD.trans e'.eD
  eV := e.eV.trans e'.eV
  smul := by
    intro g d
    show e'.eD (e.eD (g • d)) = e'.eG (e.eG g) • e'.eD (e.eD d)
    rw [e.smul, e'.smul]
  rho := by
    intro g x
    show e'.eV (e.eV (S.ρ g x)) = S''.ρ (e'.eG (e.eG g)) (e'.eV (e.eV x))
    rw [e.rho, e'.rho]
  pair := by
    intro x y
    show S''.pair (e'.eV (e.eV x)) (e'.eV (e.eV y)) = _
    rw [e'.pair, e.pair]
  nab := by
    intro d
    show S''.Nab (e'.eD (e.eD d)) = _
    rw [e'.nab, e.nab, ← Submodule.map_comp]
    rfl
  del := by
    intro d
    show S''.Del (e'.eD (e.eD d)) = _
    rw [e'.del, e.del, ← Submodule.map_comp]
    rfl
  rat := rat_comp S.bV S'.bV S''.bV (e.eV : S.V →ₗ[K] S'.V) (e'.eV : S'.V →ₗ[K] S''.V) (cmMax K) e.rat e'.rat
  rat_symm := rat_comp S''.bV S'.bV S.bV (e'.eV.symm : S''.V →ₗ[K] S'.V) (e.eV.symm : S'.V →ₗ[K] S.V) (cmMax K)
    e'.rat_symm e.rat_symm

end GSD.Iso

namespace LocOp

end LocOp

namespace GSD

variable (S : GSD K)

@[reducible] def restr (T : SubMulAction S.G S.D) : GSD K where
  G := S.G
  D := T
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab := fun t => S.Nab (t : S.D)
  Del := fun t => S.Del (t : S.D)

theorem restr_cls_eq_iff (T : SubMulAction S.G S.D) (t t' : T) :
    (S.restr T).cls t = (S.restr T).cls t' ↔ S.cls (t : S.D) = S.cls (t' : S.D) := by
  rw [GSD.cls_eq_iff, GSD.cls_eq_iff]
  exact exists_congr fun g => ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

variable (A : Type) [Group A] [MulAction A S.D]

structure Slice where
  T : SubMulAction S.G S.D
  uniq : ∀ d : S.D, ∃! a : A, a • d ∈ T

namespace Slice

variable {S A} (σ : S.Slice A)

def a (d : S.D) : A := (σ.uniq d).choose

theorem a_mem (d : S.D) : σ.a d • d ∈ σ.T := by
  exact (σ.uniq d).choose_spec.1

theorem a_eq {d : S.D} {b : A} (hb : b • d ∈ σ.T) : σ.a d = b := by
  exact ((σ.uniq d).choose_spec.2 b hb).symm

def glue (F : A → (S.restr σ.T).EqFun) (d : S.D) : S.V :=
  ((F (σ.a d)⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨σ.a d • d, σ.a_mem d⟩

theorem glue_eq (F : A → (S.restr σ.T).EqFun) (d : S.D) (b : A) (hb : b • d ∈ σ.T) :
    σ.glue F d = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
  have e := σ.a_eq hb
  have aux : ∀ (c : A) (_ : b = c) (t' : σ.T) (_ : (t' : S.D) = b • d),
      ((F c⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b⁻¹ : (S.restr σ.T).EqFun) : σ.T → S.V) ⟨b • d, hb⟩ := by
    rintro _ rfl t' ht
    obtain rfl : t' = ⟨b • d, hb⟩ := Subtype.ext ht
    rfl
  exact aux _ e.symm _ (show σ.a d • d = b • d by rw [e])

variable [SMulCommClass A S.G S.D]

def split : S.EqFun ≃ₗ[K] (A → (S.restr σ.T).EqFun) where
  toFun φ b := ⟨fun t => (φ : S.D → S.V) (b • ((t : σ.T) : S.D)), fun (g : S.G) t => by
    show (φ : S.D → S.V) (b • g • ((t : σ.T) : S.D)) = S.ρ g ((φ : S.D → S.V) (b • ((t : σ.T) : S.D)))
    rw [smul_comm, φ.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨σ.glue F, fun g d => by
    have hb : σ.a d • g • d ∈ σ.T := by
      rw [smul_comm]
      exact σ.T.smul_mem g (σ.a_mem d)
    rw [σ.glue_eq F (g • d) (σ.a d) hb]
    have h1 := (F (σ.a d)⁻¹).2 g ⟨σ.a d • d, σ.a_mem d⟩
    have h2 : (⟨σ.a d • g • d, hb⟩ : σ.T) = g • (⟨σ.a d • d, σ.a_mem d⟩ : σ.T) :=
      Subtype.ext (smul_comm _ _ _)
    rw [h2]
    exact h1⟩
  left_inv φ := by
    apply Subtype.ext
    funext d
    show (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) = (φ : S.D → S.V) d
    rw [inv_smul_smul]
  right_inv F := by
    funext b
    apply Subtype.ext
    funext t
    have hb : b⁻¹ • b • ((t : σ.T) : S.D) ∈ σ.T := by
      rw [inv_smul_smul]
      exact (t : σ.T).2
    show σ.glue F (b • ((t : σ.T) : S.D)) = _
    rw [σ.glue_eq F _ b⁻¹ hb]
    have aux : ∀ (c : A) (_ : c = b) (t' : σ.T) (_ : t' = t),
        ((F c : (S.restr σ.T).EqFun) : σ.T → S.V) t' = ((F b : (S.restr σ.T).EqFun) : σ.T → S.V) t := by
      rintro _ rfl _ rfl
      rfl
    exact aux _ (inv_inv b) _ (Subtype.ext (inv_smul_smul _ _))

theorem split_apply (φ : S.EqFun) (b : A) (t : σ.T) :
    ((σ.split φ b : (S.restr σ.T).EqFun) : σ.T → S.V) t = (φ : S.D → S.V) (b • (t : S.D)) := rfl

def dia (S : GSD K) {A : Type} [Group A] [MulAction A S.D] [SMulCommClass A S.G S.D] (b : A) : LocOp S S :=
  LocOp.ofMap (MonoidHom.id S.G) (fun d => b • d) LinearMap.id (fun g d => smul_comm b g d) (fun _ _ => rfl)

theorem split_mem_intOf (N : S.D → Submodule (𝓞 K) S.V) (hN : ∀ (b : A) (d : S.D), N (b • d) = N d) (φ : S.EqFun) :
    φ ∈ S.intOf N ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intOf (fun t => N ((t : σ.T) : S.D)) := by
  constructor
  · intro hφ b t
    show (φ : S.D → S.V) (b • (t : S.D)) ∈ N (t : S.D)
    rw [← hN b]
    exact hφ _
  · intro H d
    have h1 : (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) ∈ N (σ.a d • d) := H (σ.a d)⁻¹ ⟨σ.a d • d, σ.a_mem d⟩
    rw [inv_smul_smul, hN] at h1
    exact h1

def clEquiv (sT : (S.restr σ.T).Sec) : A × (S.restr σ.T).Cl ≃ S.Cl :=
  Equiv.ofBijective (fun p => S.cls (p.1 • ((sT.rep p.2 : σ.T) : S.D))) (by
    have := SMulCommClass.symm A S.G S.D
    constructor
    · rintro ⟨b, c⟩ ⟨b', c'⟩ hp
      obtain ⟨g, hg⟩ := (S.cls_eq_iff _ _).mp hp
      have hg' : g • b' • ((sT.rep c' : σ.T) : S.D) = b • ((sT.rep c : σ.T) : S.D) := hg
      have h1 : (b⁻¹ * b') • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [mul_smul, smul_comm b' g, hg', inv_smul_smul]
        exact (sT.rep c : σ.T).2
      have h2 : (1 : A) • (g • ((sT.rep c' : σ.T) : S.D)) ∈ σ.T := by
        rw [one_smul]
        exact σ.T.smul_mem g (sT.rep c' : σ.T).2
      have h3 : b⁻¹ * b' = 1 := (σ.a_eq h1).symm.trans (σ.a_eq h2)
      have h4 : b' = b := (inv_mul_eq_one.mp h3).symm
      subst h4
      rw [smul_comm] at hg'
      have h5 := MulAction.injective b' hg'
      have h6 : (S.restr σ.T).cls (sT.rep c) = (S.restr σ.T).cls (sT.rep c') :=
        (S.restr_cls_eq_iff σ.T _ _).mpr ((S.cls_eq_iff _ _).mpr ⟨g, h5⟩)
      rw [sT.spec, sT.spec] at h6
      rw [h6]
    · intro c
      obtain ⟨d, rfl⟩ : ∃ d, S.cls d = c := ⟨Quotient.out c, Quotient.out_eq c⟩
      let t : σ.T := ⟨σ.a d • d, σ.a_mem d⟩
      refine ⟨((σ.a d)⁻¹, (S.restr σ.T).cls t), ?_⟩
      obtain ⟨g, hg⟩ : ∃ g : S.G, g • (sT.rep ((S.restr σ.T).cls t) : σ.T) = t := sT.exists_mv t
      have hg' : g • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D) = σ.a d • d := congrArg Subtype.val hg
      show S.cls ((σ.a d)⁻¹ • ((sT.rep ((S.restr σ.T).cls t) : σ.T) : S.D)) = S.cls d
      rw [← S.cls_smul g, smul_comm, hg', inv_smul_smul])

def sec (sT : (S.restr σ.T).Sec) : S.Sec where
  rep := fun c => ((σ.clEquiv sT).symm c).1 • ((sT.rep ((σ.clEquiv sT).symm c).2 : σ.T) : S.D)
  spec := fun c => (σ.clEquiv sT).apply_symm_apply c

end Slice

end GSD

section Fib

variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)

def fibre (x : D₀) : SubMulAction (MulAction.stabilizer G x) D where
  carrier := {d | pr d = x}
  smul_mem' := by
    intro γ d hd
    show pr ((γ : G) • d) = x
    rw [hpr, show pr d = x from hd]
    exact γ.2

def orbitsFib (rep : MulAction.orbitRel.Quotient G D₀ → D₀)
    (hrep : ∀ c, (Quotient.mk'' (rep c) : MulAction.orbitRel.Quotient G D₀) = c) :
    (Σ c : MulAction.orbitRel.Quotient G D₀,
      MulAction.orbitRel.Quotient (MulAction.stabilizer G (rep c)) (fibre pr hpr (rep c))) ≃
      MulAction.orbitRel.Quotient G D :=
  Equiv.ofBijective
    (fun p => Quotient.map' (s₂ := MulAction.orbitRel G D) (fun y : fibre pr hpr (rep p.1) => (y : D))
      (by
        rintro y y' ⟨γ, hγ⟩
        exact ⟨(γ : G), congrArg Subtype.val hγ⟩) p.2)
    (by
      constructor
      · rintro ⟨c, q⟩ ⟨c', q'⟩ h
        induction q using Quotient.inductionOn' with
        | h y =>
        induction q' using Quotient.inductionOn' with
        | h y' =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • (y' : D) = (y : D) := Quotient.exact' h
        have h1 : g • rep c' = rep c := by
          rw [← show pr (y' : D) = rep c' from y'.2, ← hpr, hg]
          exact y.2
        have hc : c = c' := by
          rw [← hrep c, ← hrep c']
          exact Quotient.sound' ⟨g, h1⟩
        subst hc
        refine congrArg (Sigma.mk c) (Quotient.sound' ⟨⟨g, h1⟩, Subtype.ext hg⟩)
      · intro q
        induction q using Quotient.inductionOn' with
        | h d =>
        obtain ⟨g, hg⟩ : ∃ g : G, g • pr d = rep (Quotient.mk'' (pr d)) := Quotient.exact' (hrep (Quotient.mk'' (pr d)))
        refine ⟨⟨Quotient.mk'' (pr d), Quotient.mk'' ⟨g • d, (hpr g d).trans hg⟩⟩, ?_⟩
        exact Quotient.sound' ⟨g, rfl⟩)

theorem fibre_card_stab (x : D₀) (y : fibre pr hpr x) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G x) y) = Nat.card (MulAction.stabilizer G (y : D)) := by
  have h1 : ∀ γ : MulAction.stabilizer (MulAction.stabilizer G x) y,
      ((γ : MulAction.stabilizer G x) : G) ∈ MulAction.stabilizer G (y : D) := fun γ =>
    MulAction.mem_stabilizer_iff.mpr (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp γ.2))
  have hy : pr (y : D) = x := y.2
  have h2 : ∀ g : MulAction.stabilizer G (y : D), (g : G) ∈ MulAction.stabilizer G x := by
    intro g
    have hg : (g : G) • (y : D) = y := MulAction.mem_stabilizer_iff.mp g.2
    refine MulAction.mem_stabilizer_iff.mpr ?_
    calc (g : G) • x = (g : G) • pr (y : D) := by rw [hy]
      _ = pr ((g : G) • (y : D)) := (hpr _ _).symm
      _ = pr (y : D) := by rw [hg]
      _ = x := hy
  have h3 : ∀ g : MulAction.stabilizer G (y : D),
      (⟨(g : G), h2 g⟩ : MulAction.stabilizer G x) ∈ MulAction.stabilizer (MulAction.stabilizer G x) y := fun g =>
    MulAction.mem_stabilizer_iff.mpr (Subtype.ext (MulAction.mem_stabilizer_iff.mp g.2))
  exact Nat.card_congr ⟨fun γ => ⟨_, h1 γ⟩, fun g => ⟨_, h3 g⟩, fun γ => rfl, fun g => rfl⟩

end Fib

theorem ClsKer.opOf_mem_intOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (n : ℕ) (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : (n : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by
  intro d'
  show (n : 𝓞 K) • A.appOf h s φ d' ∈ N' d'
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨m, hm⟩ := hn c
  have hw : (((S.toCSDOf h s).wt c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by unfold CSD.wt; exact @Fintype.card_ne_zero _ ((S.toCSDOf h s).finGam c) ⟨1⟩)
  have e1 : ((n : 𝓞 K) • ((((S.toCSDOf h s).wt c : ℕ) : K))⁻¹) = ((m : ℕ) : K) := by
    rw [Algebra.smul_def, map_natCast, hm, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rw [← smul_assoc, e1, Nat.cast_smul_eq_nsmul]
  exact (N' d').nsmul_mem (hk _ d' _ (hφ _)) m

namespace GSD

variable (S : GSD K)

theorem ipOf_eq_csOf (h : S.Ok) (s : S.Sec) (φ ψ : S.D → S.V) :
    S.ipOf h s φ ψ = S.csOf h s fun d => S.pair (φ d) (ψ d) := rfl

end GSD

theorem ClsKer.appOf_eq_csOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (φ : S.D → S.V) (d' : S'.D) :
    A.appOf h s φ d' = S.csOf h s fun d => A.k d d' (φ d) := rfl

namespace BiPair

variable {S S' : GSD K} (P : BiPair S S')

theorem formOf_apply (h' : S'.Ok) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.formOf h' s' φ ψ = P.sumOf h' s' φ ψ := rfl

end BiPair

namespace GFam

variable (F : GFam K)

theorem wt_eq (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (c : F.Cl) :
    (F.toCSDOf h s).wt c = ((F.mem c.1).toCSDOf (h c.1) (s c.1)).wt c.2 := rfl

end GFam

namespace GSD

end GSD

end Formalism.L2.Col
