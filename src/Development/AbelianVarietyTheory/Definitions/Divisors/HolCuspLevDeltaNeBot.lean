import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AbelianVarietyTheory.Definitions.Divisors.HoloOcc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformModel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix

namespace GlobalTheory.TfJl

section Hecke

variable {G : Type} [Group G]

@[ext] structure HeckeFn (U : Subgroup G) where

  toFun : G → ℂ
  left : ∀ u ∈ U, ∀ g, toFun (u * g) = toFun g
  right : ∀ u ∈ U, ∀ g, toFun (g * u) = toFun g
  fin : {q : G ⧸ U | toFun q.out ≠ 0}.Finite

open Classical in

def dcFn (U : Subgroup G) (x : G) : G → ℂ := fun g => if ∃ a ∈ U, ∃ b ∈ U, g = a * x * b then 1 else 0

theorem dcFn_left (U : Subgroup G) (x : G) {u : G} (hu : u ∈ U) (g : G) : dcFn U x (u * g) = dcFn U x g := by
  classical
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨u⁻¹ * a, U.mul_mem (U.inv_mem hu) ha, b, hb, by rw [mul_assoc, mul_assoc, ← mul_assoc a, ← e, inv_mul_cancel_left]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨u * a, U.mul_mem hu ha, b, hb, by simp only [mul_assoc]⟩

theorem dcFn_right (U : Subgroup G) (x : G) {u : G} (hu : u ∈ U) (g : G) : dcFn U x (g * u) = dcFn U x g := by
  classical
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, b * u⁻¹, U.mul_mem hb (U.inv_mem hu), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * u, U.mul_mem hb hu, by simp only [mul_assoc]⟩

theorem dcFn_fin [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G} (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G))
    (x : G) : {q : G ⧸ U | dcFn U x q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology ho
  have h : IsCompact ((fun a : G => ((a * x : G) : G ⧸ U)) '' U) :=
    hc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))
  refine h.finite_of_discrete.subset fun q hq => ?_
  have hq' : ∃ a ∈ U, ∃ b ∈ U, q.out = a * x * b := by
    by_contra hn
    exact hq (if_neg hn)
  obtain ⟨a, ha, b, hb, e⟩ := hq'
  refine ⟨a, ha, ?_⟩
  rw [← QuotientGroup.out_eq' q, e]
  exact (QuotientGroup.mk_mul_of_mem _ hb).symm

namespace HeckeFn

variable {U : Subgroup G} (f : HeckeFn U)

theorem apply_out (g : G) : f.toFun ((g : G ⧸ U).out) = f.toFun g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hh]; exact f.right _ h.2 g

def supp : Finset (G ⧸ U) := f.fin.toFinset

theorem mem_supp {q : G ⧸ U} : q ∈ f.supp ↔ f.toFun q.out ≠ 0 := f.fin.mem_toFinset

theorem mk_mem_supp {g : G} : (g : G ⧸ U) ∈ f.supp ↔ f.toFun g ≠ 0 := by rw [mem_supp, apply_out]

open Classical in

def one (U : Subgroup G) : HeckeFn U where
  toFun g := if g ∈ U then 1 else 0
  left u hu g := if_congr (U.mul_mem_cancel_left hu) rfl rfl
  right u hu g := if_congr (U.mul_mem_cancel_right hu) rfl rfl
  fin := (Set.finite_singleton (((1 : G)) : G ⧸ U)).subset fun q hq => by
    have h : q.out ∈ U := by
      by_contra hn
      exact hq (if_neg hn)
    rw [Set.mem_singleton_iff, ← QuotientGroup.out_eq' q, ← one_mul q.out]
    exact QuotientGroup.mk_mul_of_mem _ h

def dc [TopologicalSpace G] [IsTopologicalGroup G] (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) (x : G) : HeckeFn U :=
  ⟨dcFn U x, fun _ hu => dcFn_left U x hu, fun _ hu => dcFn_right U x hu, dcFn_fin ho hc x⟩

instance : Inhabited (HeckeFn U) := ⟨one U⟩

end HeckeFn

variable {U : Subgroup G} {M : Type} [AddCommGroup M] [Module ℂ M]

def heckeOp (ρ : Representation ℂ G M) (f : HeckeFn U) : Module.End ℂ M := ∑ q ∈ f.supp, f.toFun q.out • ρ q.out

theorem heckeOp_apply (ρ : Representation ℂ G M) (f : HeckeFn U) (m : M) :
    heckeOp ρ f m = ∑ q ∈ f.supp, f.toFun q.out • ρ q.out m := by
  simp [heckeOp, LinearMap.sum_apply]

theorem heckeOp_term (ρ : Representation ℂ G M) (f : HeckeFn U) {m : M} (hm : m ∈ Hi.fixd ρ U) (g : G) :
    f.toFun (g : G ⧸ U).out • ρ (g : G ⧸ U).out m = f.toFun g • ρ g m := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hh, f.right _ h.2, map_mul, Module.End.mul_apply, hm _ h.2]

theorem heckeOp_mem_fixd (ρ : Representation ℂ G M) (f : HeckeFn U) {m : M} (hm : m ∈ Hi.fixd ρ U) : heckeOp ρ f m ∈ Hi.fixd ρ U := by
  intro u hu
  have hq : ∀ q : G ⧸ U, MulAction.toPerm u q = ((u * q.out : G) : G ⧸ U) := fun q => by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [heckeOp_apply, map_sum]
  refine Finset.sum_equiv (MulAction.toPerm u) (fun q => ?_) fun q _ => ?_
  · rw [hq, f.mk_mem_supp, f.left u hu, f.mem_supp]
  · rw [hq, heckeOp_term ρ f hm, f.left u hu, map_smul, map_mul, Module.End.mul_apply]

theorem heckeOp_mem_of_stable (ρ : Representation ℂ G M) (f : HeckeFn U) {W : Submodule ℂ M} (hW : ∀ g, ∀ m ∈ W, ρ g m ∈ W) {m : M}
    (hm : m ∈ W) : heckeOp ρ f m ∈ W := by
  rw [heckeOp_apply]
  exact W.sum_mem fun q _ => W.smul_mem _ (hW _ m hm)

def heckeOn (ρ : Representation ℂ G M) {W : Submodule ℂ M} (hW : ∀ g, ∀ m ∈ W, ρ g m ∈ W) (f : HeckeFn U) :
    Module.End ℂ ↥(W ⊓ Hi.fixd ρ U) :=
  (heckeOp ρ f).restrict fun _ h => ⟨heckeOp_mem_of_stable ρ f hW h.1, heckeOp_mem_fixd ρ f h.2⟩

end Hecke

section Casimir

private theorem qdet_two' {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem casimir' {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k c : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = c • φ)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (c + k - 1) / 2) * (u + (c - k + 1) / 2)) • φ := by
  have hI := Complex.I_mul_I
  have hc : E 1 0 φ = E 0 1 φ - (Complex.I * k) • φ := by rw [← h1]; abel
  have ha : E 0 0 φ = Complex.I • E 0 1 φ + ((k + c) / 2) • φ := by
    rw [hc] at h2
    linear_combination (norm := skip) (1 / 2 : ℂ) • h0 + (1 / 2 : ℂ) • h2
    match_scalars <;> first | ring1 | linear_combination (k / 2) * hI | linear_combination (-k / 2) * hI
  have hd : E 1 1 φ = c • φ - E 0 0 φ := by rw [← h0]; abel
  have r1 : E 0 0 (E 0 1 φ) = E 0 1 (E 0 0 φ) + E 0 1 φ := by
    have := LinearMap.congr_fun (hE 0 0 0 1) φ
    simp at this
    exact sub_eq_iff_eq_add'.1 this
  have r2 : E 1 0 (E 0 1 φ) = E 0 1 (E 1 0 φ) + (E 1 1 φ - E 0 0 φ) := by
    have := LinearMap.congr_fun (hE 1 0 0 1) φ
    simp at this
    rw [← this]; abel
  have r3 : E 0 0 (E 0 0 φ) = Complex.I • E 0 0 (E 0 1 φ) + ((k + c) / 2) • E 0 0 φ := by
    conv_lhs => rw [ha]
    simp
  rw [qdet_two']
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add,
    map_smul, hd, map_sub, r2, r3, r1]
  simp only [hc, ha, map_add, map_smul, map_sub]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

end Casimir

section Hol

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def cw (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) : ℤ := -((lam v).w 0 + (lam v).w 1)

omit [NumberField F] [IsTotallyReal F] in

theorem two_le_kw (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) : 2 ≤ kw lam v := by
  have := (lam v).anti (show (0 : Fin 2) ≤ 1 by decide)
  unfold kw; omega

def kn (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) : ℕ := (kw lam v).toNat

omit [NumberField F] [IsTotallyReal F] in

@[simp] theorem kn_cast (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) : (kn lam v : ℤ) = kw lam v :=
  Int.toNat_of_nonneg (by have := two_le_kw lam v; omega)

omit [NumberField F] [IsTotallyReal F] in

theorem infChar_prod (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) (u : ℂ) :
    (((GlobalTheory.UnitaryBC.infOfWeight (lam v)).map Neg.neg).map (u + ·)).prod =
      (u + ((cw lam v : ℂ) + kw lam v - 1) / 2) * (u + ((cw lam v : ℂ) - kw lam v + 1) / 2) := by
  rw [GlobalTheory.UnitaryBC.infOfWeight, Multiset.map_map, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fin.prod_univ_two]
  simp only [cw, kw, Function.comp]
  push_cast
  simp
  ring

theorem isHolo_iff (lam : InfinitePlace F → DomWeight 2) (φ : TR.Sm F 2) :
    IsHolo lam φ ↔ TR.IsCuspForm φ ∧ ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (kw lam v : ℂ)) • φ ∧
      TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ) ∧
      TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = (cw lam v : ℂ) • φ := by
  refine and_congr_right fun _ => forall_congr' fun v => and_congr_right fun h1 => and_congr_right fun h2 => ⟨fun h => ?_, fun h u => ?_⟩
  · have h0 := h 0
    have h1 := h 1
    rw [infChar_prod] at h0 h1
    simp only [TR.cap, qdet_two', LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      Module.algebraMap_end_apply, map_add, map_smul] at h0 h1
    push_cast at h0 h1
    linear_combination (norm := module) h1 - h0
  · rw [infChar_prod, ← casimir' _ (TR.glRel_Eop v) _ _ φ h h1 h2 u, TR.cap]
    norm_num

theorem Eop_finRep (v : InfinitePlace F) (i j : Fin 2) (g : GF F) (φ : TR.Sm F 2) :
    TR.Eop v i j (TR.finRep F 2 g φ) = TR.finRep F 2 g (TR.Eop v i j φ) :=
  LinearMap.congr_fun (TR.lie_rt_fin _ g) φ

def holCusp (lam : InfinitePlace F → DomWeight 2) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHolo lam φ}
  add_mem' {φ ψ} h h' := by
    refine ⟨Fb.mem_range_ofCusp.1 (add_mem (Fb.mem_range_ofCusp.2 h.1) (Fb.mem_range_ofCusp.2 h'.1)), fun v => ⟨?_, ?_, fun u => ?_⟩⟩
    · simp only [map_add]
      linear_combination (norm := module) (h.2 v).1 + (h'.2 v).1
    · simp only [map_add]
      linear_combination (norm := module) (h.2 v).2.1 + (h'.2 v).2.1
    · rw [map_add, (h.2 v).2.2, (h'.2 v).2.2, smul_add]
  zero_mem' := ⟨Fb.mem_range_ofCusp.1 (zero_mem _), fun v => by simp⟩
  smul_mem' c φ h := by
    refine ⟨Fb.mem_range_ofCusp.1 (Submodule.smul_mem _ c (Fb.mem_range_ofCusp.2 h.1)), fun v => ⟨?_, ?_, fun u => ?_⟩⟩
    · simp only [map_smul]
      linear_combination (norm := module) c • (h.2 v).1
    · simp only [map_smul]
      linear_combination (norm := module) c • (h.2 v).2.1
    · rw [map_smul, (h.2 v).2.2, smul_comm]

@[simp] theorem mem_holCusp {lam : InfinitePlace F → DomWeight 2} {φ : TR.Sm F 2} : φ ∈ holCusp lam ↔ IsHolo lam φ := Iff.rfl

theorem finRep_mem_holCusp (lam : InfinitePlace F → DomWeight 2) (g : GF F) (φ : TR.Sm F 2) (h : φ ∈ holCusp lam) :
    TR.finRep F 2 g φ ∈ holCusp lam := by
  rw [mem_holCusp, isHolo_iff] at h ⊢
  refine ⟨Fb.isCuspForm_act (.fin g) h.1, fun v => ?_⟩
  simp only [Eop_finRep]
  rw [← map_sub, ← map_sub, ← map_add, ← map_add, (h.2 v).1, (h.2 v).2.1, (h.2 v).2.2, map_smul, map_smul, map_smul]
  exact ⟨rfl, rfl, rfl⟩

def holCuspLev (lam : InfinitePlace F → DomWeight 2) (U : Subgroup (GF F)) : Submodule ℂ (TR.Sm F 2) :=
  holCusp lam ⊓ Hi.fixd (TR.finRep F 2) U

def heckeHol (lam : InfinitePlace F → DomWeight 2) {U : Subgroup (GF F)} (f : HeckeFn U) : Module.End ℂ (holCuspLev lam U) :=
  heckeOn (TR.finRep F 2) (finRep_mem_holCusp lam) f

@[simp] theorem heckeHol_val (lam : InfinitePlace F → DomWeight 2) {U : Subgroup (GF F)} (f : HeckeFn U) (φ : holCuspLev lam U) :
    (heckeHol lam f φ).1 = heckeOp (TR.finRep F 2) f φ.1 := rfl

end Hol

section Iwahori

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] (w : Pl F)

def iwa : Subgroup (GL (Fin 2) (w.adicCompletion F)) := GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin 2)

theorem isOpen_iwa : IsOpen (iwa w : Set (GL (Fin 2) (w.adicCompletion F))) := GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _

theorem isCompact_iwa : IsCompact (iwa w : Set (GL (Fin 2) (w.adicCompletion F))) := GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _

def tEnt (m : ℤ) : Fin 2 → (w.adicCompletion F)ˣ := fun i => atFin w (unif w) ^ (![m, -m] i)

def tDiag (m : ℤ) : GL (Fin 2) (w.adicCompletion F) := GlobalTheory.SmGL.diagT (w.adicCompletion F) (Fin 2) (tEnt w m)

def iwaInd (m : ℤ) : GL (Fin 2) (w.adicCompletion F) → ℂ := dcFn (iwa w) (tDiag w m)

def iwaHecke (m : ℤ) : HeckeFn (iwa w) := HeckeFn.dc (isOpen_iwa w) (isCompact_iwa w) (tDiag w m)

@[simp] theorem iwaHecke_toFun (m : ℤ) : (iwaHecke w m).toFun = iwaInd w m := rfl

end Iwahori

section Tens

variable {F : Type} [Field F] [NumberField F] (w : Pl F)

def atW : GF F →* GL (Fin 2) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (pLoc F w)

theorem gf_ext {g h : GF F} (e : ∀ v, atW v g = atW v h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun x : GL (Fin 2) (v.adicCompletion F) => x i j) (e v)

@[simp] theorem atW_locGL (x : GL (Fin 2) (w.adicCompletion F)) : atW w (locGL F 2 w x) = x := pLoc_locGL w x

theorem atW_locGL_of_ne {v : Pl F} (h : v ≠ w) (x : GL (Fin 2) (w.adicCompletion F)) : atW v (locGL F 2 w x) = 1 :=
  pLoc_locGL_of_ne h x

def awayW : GF F →* GF F where
  toFun g := g * (locGL F 2 w (atW w g))⁻¹
  map_one' := by simp
  map_mul' g h := gf_ext fun v => by
    by_cases e : v = w
    · subst e; simp
    · simp [atW_locGL_of_ne w e]

@[simp] theorem atW_awayW (g : GF F) : atW w (awayW w g) = 1 := by simp [awayW]

@[simp] theorem awayW_locGL (x : GL (Fin 2) (w.adicCompletion F)) : awayW w (locGL F 2 w x) = 1 := by simp [awayW]

@[simp] theorem awayW_awayW (g : GF F) : awayW w (awayW w g) = awayW w g := by
  change awayW w g * (locGL F 2 w (atW w (awayW w g)))⁻¹ = _
  simp

def levAt (U : Subgroup (GF F)) (K : Subgroup (GL (Fin 2) (w.adicCompletion F))) : Subgroup (GF F) :=
  U.comap (awayW w) ⊓ K.comap (atW w)

theorem mem_levAt {U : Subgroup (GF F)} {K : Subgroup (GL (Fin 2) (w.adicCompletion F))} {g : GF F} :
    g ∈ levAt w U K ↔ awayW w g ∈ U ∧ atW w g ∈ K := Iff.rfl

def HeckeFn.tensAt {U : Subgroup (GF F)} {K : Subgroup (GL (Fin 2) (w.adicCompletion F))} (f : HeckeFn U) (h : HeckeFn K) :
    HeckeFn (levAt w U K) where
  toFun g := f.toFun (awayW w g) * h.toFun (atW w g)
  left u hu g := by rw [map_mul, map_mul, f.left _ hu.1, h.left _ hu.2]
  right u hu g := by rw [map_mul, map_mul, f.right _ hu.1, h.right _ hu.2]
  fin := by
    refine Set.Finite.of_finite_image (f := fun q => (((awayW w q.out : GF F) : GF F ⧸ U), ((atW w q.out : GL (Fin 2) _) : _ ⧸ K)))
      ((f.supp ×ˢ h.supp).finite_toSet.subset ?_) fun q _ q' _ e => ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact Finset.mem_product.2 ⟨f.mk_mem_supp.2 (left_ne_zero_of_mul hq), h.mk_mem_supp.2 (right_ne_zero_of_mul hq)⟩
    · rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, mem_levAt, map_mul, map_mul, map_inv, map_inv]
      exact ⟨QuotientGroup.eq.1 (congrArg Prod.fst e), QuotientGroup.eq.1 (congrArg Prod.snd e)⟩

@[simp] theorem HeckeFn.tensAt_apply {U : Subgroup (GF F)} {K : Subgroup (GL (Fin 2) (w.adicCompletion F))} (f : HeckeFn U)
    (h : HeckeFn K) (g : GF F) : (f.tensAt w h).toFun g = f.toFun (awayW w g) * h.toFun (atW w g) := rfl

end Tens

end GlobalTheory.TfJl
