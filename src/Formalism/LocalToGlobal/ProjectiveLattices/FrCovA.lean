import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

noncomputable section

namespace Formalism.L2.Pj.FrCov

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

section Comb

variable {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
  {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}

theorem comb_uniq (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  unfold IsCombAt at h h'
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [e]

def ρD (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : tEps (spMap ψ ≫ x) ⟶ tEps x :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem eps_dual (ψ : S →+* T) (a : S) : spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem comb_bc (ψ : S →+* T) (h : IsCombAt x v cf w) :
    IsCombAt (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (cf j)) (spMap (dualMap ψ) ≫ w) := by
  unfold IsCombAt at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  have key : ∀ l : List (tEps x ⟶ Xo.univ.t.G), (l.map (fun g => ρD ψ x ≫ g)).prod = ρD ψ x ≫ l.prod := by
    intro l
    induction l with
    | nil =>
      first | simp [comp_one] | simp [MonObj.comp_one] | simp [Hom.comp_one] | simp
    | cons a l ih =>
      first | simp [ih, comp_mul] | simp [ih, MonObj.comp_mul] | simp [ih, Hom.comp_mul] | simp [ih]
  refine ⟨fun i => ρD ψ x ≫ u i, fun i => ?_, ?_⟩
  · rw [Over.comp_left, hu i]
    show spMap (dualMap ψ) ≫ spMap (epsMul (cf i)) ≫ v i = _
    rw [← Category.assoc, eps_dual, Category.assoc]
  · have e2 : (List.ofFn fun i => ρD ψ x ≫ u i) = (List.ofFn u).map (fun g => ρD ψ x ≫ g) := by
      first | (rw [List.map_ofFn]; rfl) | simp [List.map_ofFn, Function.comp_def]
    rw [e2, key, Over.comp_left]
    rfl

def resM (ψ : S →+* T) (n : TanM x Xo.univ.t.G) : TanM (spMap ψ ≫ x) Xo.univ.t.G :=
  mkT (ρD ψ x ≫ tv n) (smT_zero_ovT (t := Xo.univ.t) (tan_bc ψ (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n))))

end Comb

variable (hS' : Out.SecBaseChangeAnySt) (hT : Out.SecTwistSt) {R T T' : Type} [CommRing R] [Algebra c.F R] [CommRing T]
  [Algebra c.F T] [CommRing T'] [Algebra c.F T']

def bc (ψ : R →ₐ[c.F] T) (y : FrPt Xo c R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over, sOf, sOf, spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    exact ψ.comp_algebraMap
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis := bcLieAll c ψ y
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frameR hS' hT y.x ψ.toRingHom y.s y.gen

abbrev Mx (Dw : Datum H) (T : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T

def Rl (y : FrPt Xo c R) (a : R →ₐ[c.F] T) (M : Mx Dw T) (t : T) (z : FrPt Xo c T) : Prop :=
  z.x = spMap a.toRingHom ≫ y.x ∧
    (∀ τ i, IsCombAt (spMap a.toRingHom ≫ y.x) (fun j => spMap (dualMap a.toRingHom) ≫ y.u τ j) (M τ i) (z.u τ i)) ∧
    ∃ pm : Gx z.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap a.toRingHom ∧
      ∀ i, ∀ p ∈ (PPx z.x).U i, gs (𝟙 _) p _ (z.s.f i) = cst (fst (Over.mk z.x) Xo.univ.t.G).left p t * gs pm p _ (y.s.f i)

variable {y : FrPt Xo c R} {a : R →ₐ[c.F] T} {M M' N : Mx Dw T} {t t' r : T} {z z' : FrPt Xo c T} {w : FrPt Xo c T'}

theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (h₁ : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left) : p = q := by
  apply pullback.hom_ext
  · first | exact h₁ | simpa using h₁
  · first | exact h₂ | simpa using h₂

theorem exists_pm {S S' : Type} [CommRing S] [CommRing S'] {x : Sp S ⟶ Xo.X} {x' : Sp S' ⟶ Xo.X} (g : Sp S' ⟶ Sp S)
    (h : x' = g ≫ x) : ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ g := by
  subst h
  refine ⟨pullback.lift ((fst (Over.mk (g ≫ x)) Xo.univ.t.G).left ≫ g) (snd (Over.mk (g ≫ x)) Xo.univ.t.G).left ?_, ?_, ?_⟩
  · rw [Category.assoc]
    exact pullback.condition
  · exact pullback.lift_snd _ _ _
  · exact pullback.lift_fst _ _ _

theorem Rl.map (ψ : T →ₐ[c.F] T') (h : Rl y a M t z) :
    FrMap ψ z w ↔ Rl y (ψ.comp a) (fun τ => (M τ).map ψ) (ψ t) w := by
  obtain ⟨hx, hu, pm, s₁, f₁, v₁⟩ := h
  have cb := fun τ i => comb_bc ψ.toRingHom (hu τ i)
  simp only [← Category.assoc, ← spMap_algHom_comp, ← spMap_dual_comp] at cb
  have val : ∀ q : Gx w.x ⟶ Gx z.x, q ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = (snd (Over.mk w.x) Xo.univ.t.G).left →
      q ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = (fst (Over.mk w.x) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → ∀ i,
      ∀ p ∈ (PPx w.x).U i, gs q p _ (z.s.f i) = cst (fst (Over.mk w.x) Xo.univ.t.G).left p (ψ t) * gs (q ≫ pm) p _ (y.s.f i) :=
    fun q s₂ f₂ i p hp => by
      have m := ppx_le_cov q s₂ i hp
      rw [gs_stalkMap q p _ m, v₁ i _ m, map_mul, cst_stalkMap, f₂, cst_comp, ← gs_comp q pm p _ (ppx_le_cov pm s₁ i m)]; rfl
  constructor
  · rintro ⟨hx₂, hu₂, q, s₂, f₂, v₂⟩
    refine ⟨by rw [hx₂, hx, spMap_algHom_comp, Category.assoc], fun τ i => (hu₂ τ i).symm ▸ cb τ i, q ≫ pm,
      by rw [Category.assoc, s₁, s₂], by rw [Category.assoc, f₁, ← Category.assoc, f₂, Category.assoc, spMap_algHom_comp],
      fun i p hp => ?_⟩
    rw [← val q s₂ f₂ i p hp, ← v₂ i (ppx_le_cov q s₂ i), gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp]
  · rintro ⟨hx₂, hu₂, pm₂, s₂, f₂, v₂⟩
    have e : w.x = spMap ψ.toRingHom ≫ z.x := by rw [hx₂, hx, spMap_algHom_comp, Category.assoc]
    obtain ⟨q, s₃, f₃⟩ := exists_pm _ e
    refine ⟨e, fun τ i => comb_uniq (hu₂ τ i) (cb τ i), q, s₃, f₃, fun i h => fn_ext fun p hp => ?_⟩
    rw [gs_appLE q _ _ _ (𝟙 _) p hp, Category.id_comp, val q s₃ f₃ i p hp, v₂ i p hp, show q ≫ pm = pm₂ from pm_ext
      (by rw [Category.assoc, f₁, ← Category.assoc, f₃, f₂, Category.assoc, spMap_algHom_comp]) (by rw [Category.assoc, s₁, s₃, s₂])]

include hS' hT

end Formalism.L2.Pj.FrCov
