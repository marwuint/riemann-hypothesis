import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem mul_mem_UAt {X : Spc F E n} {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) :
    g * h ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, sub_mul, one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

theorem inv_mem_UAt {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    g⁻¹ ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

variable (σ) in

def KSub (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := KAt σ W v
  one_mem' := ⟨one_mem_UAt W v, fun y hy => by
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [inv_one, this, Matrix.one_mulVec]; exact ⟨hy, hy⟩⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem_UAt hg.1 hh.1, fun y hy => by
    have e1 : mat (g * h) = mat g * mat h := rfl
    have e2 : mat (h⁻¹ * g⁻¹) = mat h⁻¹ * mat g⁻¹ := rfl
    rw [mul_inv_rev, e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 y hy).1).1, (hh.2 _ (hg.2 y hy).2).2⟩⟩
  inv_mem' := fun {g} hg => ⟨inv_mem_UAt hg.1, fun y hy => by
    rw [inv_inv]; exact ⟨(hg.2 y hy).2, (hg.2 y hy).1⟩⟩

section Loc

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulW (L : IsLocRep M ψ om v ω ρ) {h h' : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) (hh' : h' ∈ UAt σ W (evFin F v))
    {φ} (hφ : φ ∈ SB _) : ω (1, h * h') φ = ω (1, h) (ω (1, h') φ) := by
  simpa using L.mul 1 (one_mem_UAt X v) h hh 1 (one_mem_UAt X v) h' hh' φ hφ

def IsLocRep.onK (L : IsLocRep M ψ om v ω ρ) : KSub σ W v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (1, k.1)).restrict fun φ hφ => L.pres 1 (one_mem_UAt X v) k.1 k.2.1 φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (L.mulW a.2.1 b.2.1 φ.2)

end Loc

end PositivityTheory.ThK
