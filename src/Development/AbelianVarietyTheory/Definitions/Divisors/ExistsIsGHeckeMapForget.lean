import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂]
  {S S' : Scheme.{0}}

def GBase.IsMap (β : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) : Prop :=
  gb₂.ρ = β gb₁.ρ ∧ ∀ i, gb₂.t i = β.comp (gb₁.t i)

def GBase.map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase G R₂ where
  ρ := β gb.ρ
  ρ_root := by simpa using congrArg β gb.ρ_root
  t i := β.comp (gb.t i)
  t_ω i := by rw [RingHom.comp_apply, gb.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map β) (gb.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [Function.comp_def] using h

theorem GBase.IsMap.id (gb : GBase G R₁) : GBase.IsMap (RingHom.id R₁) gb gb :=
  ⟨rfl, fun _ => rfl⟩

variable {R : Type} [CommRing R] [Algebra ℚ R]

section Comp

variable {R₃ : Type} [CommRing R₃] [Algebra ℚ R₃] {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {gb₃ : GBase G R₃} {N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R₁} {s₂ : S₂ ⟶ Sp R₂} {s₃ : S₃ ⟶ Sp R₃} {o₁ : GObj gb₁ N s₁}
  {o₂ : GObj gb₂ N s₂} {o₃ : GObj gb₃ N s₃} {f : S₃ ⟶ S₂} {f' : S₂ ⟶ S₁}

theorem GBase.IsMap.comp {β : R₁ →+* R₂} {β' : R₂ →+* R₃} (h' : GBase.IsMap β' gb₂ gb₃) (h : GBase.IsMap β gb₁ gb₂) :
    GBase.IsMap (β'.comp β) gb₁ gb₃ :=
  ⟨by rw [h'.1, h.1, RingHom.comp_apply], fun i => by rw [h'.2, h.2, RingHom.comp_assoc]⟩

end Comp

theorem GObj.eta_zero {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem GObj.eta_neg {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (x : G.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, GObj.eta_zero]

theorem GObj.eta_nsmul {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (n : ℕ) (x : G.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, GObj.eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def gHeckeSub {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (g : G.La →ₗ[G.O] G.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, GObj.eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, GObj.eta_neg]⟩

def IsGHecke {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : GObj gb (N * k) s)
    (o' : GObj gb N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : G.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) ∧ c ∣ k ^ 2

def IsGHeckeMap {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) (X : GenModel gb N) (X' : GenModel gb (N * k))
    (π : X'.X ⟶ X.X) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o'.A), IsGHecke g c k N X'.univ o' ψ ∧
    Nonempty (GObjMap o' X.univ π)

section API

variable {gb : GBase G R} {g : G.La →ₗ[G.O] G.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : GObj gb (N * k) s}
  {o' : GObj gb N s} {ψ : o.A ⟶ o'.A}

theorem IsGHecke.isMonHom (h : IsGHecke g c k N o o' ψ) : IsMonHom ψ := h.1

theorem IsGHecke.act (h : IsGHecke g c k N o o' ψ) (c' : G.O) : o.act.act c' ≫ ψ = ψ ≫ o'.act.act c' := h.2.1 c'

theorem IsGHecke.eta (h : IsGHecke g c k N o o' ψ) (x : G.La) : o'.eta x = o.eta (g x) ≫ ψ := h.2.2.1 x

theorem IsGHecke.cover (h : IsGHecke g c k N o o' ψ) :
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left := h.2.2.2.1

theorem IsGHecke.pol (h : IsGHecke g c k N o o' ψ) :
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) := h.2.2.2.2.1

variable {X : GenModel gb N} {X' : GenModel gb (N * k)} {π : X'.X ⟶ X.X}

end API

def GObj.forgetMul {gb : GBase G R} {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta x := o.eta (k • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, smul_smul, o.eta_ker]
  geom K _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom K x β hx
    refine ⟨I, fun y => ?_⟩
    rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N k hN hk]

theorem gHeckeSub_smul_id_eq_one {gb : GBase G R} {N k : ℕ} {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    ∀ h ∈ gHeckeSub o (k • LinearMap.id) N, h = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact o.eta_ker x

end GlobalTheory.UPel.HT.Gen
