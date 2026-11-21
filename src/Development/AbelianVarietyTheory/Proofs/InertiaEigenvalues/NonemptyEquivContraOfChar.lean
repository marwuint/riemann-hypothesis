import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology
open scoped OnePoint

namespace GlobalTheory.LocGL

namespace ProjLine

section General

variable {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X]
  [Module ℂ X] {σ : Representation ℂ G W} {π : Representation ℂ G V}

def quot (S : Subrepresentation π) : Representation ℂ G (V ⧸ S.toSubmodule) :=
  π.quotient _ fun g _ hv => S.apply_mem_toSubmodule g hv

def quotMk (S : Subrepresentation π) : π.IntertwiningMap (quot S) := ⟨S.toSubmodule.mkQ, fun _ => rfl⟩

theorem isCosocle_quot {L : Subrepresentation π} (h0 : L ≠ ⊤) (h : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤) :
    IsCosocle (quot L) π := by
  have hk : (quotMk L).ker = L := SetLike.ext fun v => Submodule.Quotient.mk_eq_zero _
  refine ⟨?_, quotMk L, L.toSubmodule.mkQ_surjective, fun S hS => ?_⟩
  · have h1 : L.toSubmodule ≠ ⊤ := fun e => h0 (Subrepresentation.toSubmodule_injective e)
    have := Submodule.Quotient.nontrivial_iff.2 h1
    have : Nontrivial (Subrepresentation (quot L)) := ⟨⊥, ⊤, fun e =>
      bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
    refine ⟨fun T => ?_⟩
    let T' : Subrepresentation π := ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
    refine (h T').imp (fun e => eq_bot_iff.2 fun y hy => ?_) fun e => eq_top_iff.2 fun y _ => ?_
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      exact (Submodule.Quotient.mk_eq_zero _).2 (e hy)
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      have : v ∈ T' := e ▸ trivial
      exact this
  · rw [hk]
    exact ((hS.le_iff.1 ((h S).resolve_right hS.1)).resolve_left h0).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem nonempty_equiv_contra_ofChar {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) :
    Nonempty ((ofChar χ⁻¹).Equiv (contra (ofChar χ))) := by
  have key : ∀ (c : ℂ) g, (ofChar χ).dual g (c • LinearMap.id) = ((χ g)⁻¹ * c : ℂ) • LinearMap.id := fun c g =>
    LinearMap.ext fun v => by
      show c • ofChar χ g⁻¹ v = _
      simp [mul_left_comm, mul_assoc]
  let f : (ofChar χ⁻¹).IntertwiningMap (contra (ofChar χ)) :=
    { toFun := fun c => ⟨c • LinearMap.id, mem_smoothPart_of_nhds (Filter.mem_of_superset (hχ.mem_nhds (one_mem _))
        fun g hg => by
          have hg' : χ g = 1 := hg
          rw [Set.mem_ofPred_eq, key, hg']
          simp)⟩
      map_add' := fun c d => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c d => Subtype.ext (mul_smul _ _ _)
      isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (Eq.trans (by simp) (key c g).symm) }
  refine ⟨equivOfBijective f ⟨fun c d h => ?_, fun l => ⟨l.1 1, Subtype.ext (LinearMap.ext fun v => ?_)⟩⟩⟩
  · simpa [f] using congrArg (fun l => l.1 1) h
  · show l.1 1 • v = l.1 v
    rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [DecidableEq k]

variable (k) in

def funRep : Representation ℂ (GL (Fin 2) k) (OnePoint k → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (g⁻¹ • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

@[simp] theorem funRep_apply (g : GL (Fin 2) k) (F : OnePoint k → ℂ) (x : OnePoint k) :
    funRep k g F x = F (g⁻¹ • x) := rfl

end ProjLine

open ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}

end GlobalTheory.LocGL
