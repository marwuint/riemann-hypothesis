import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GermSectionCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section General

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isGen_iff_gm {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

def genCast {φ φ' : K → (Y ⟶ X)} (ε : K → ℤ) (h : φ = φ') :
    LB.Gen (LB.LinComb L φ ε) ≃ LB.Gen (LB.LinComb L φ' ε) where
  toFun t := ⟨fun j => res (le_of_eq (congrArg (fun ψ => LB.wchart L ψ j) h.symm)) (t.s j)⟩
  invFun t := ⟨fun j => res (le_of_eq (congrArg (fun ψ => LB.wchart L ψ j) h)) (t.s j)⟩
  left_inv t := by
    subst h
    exact congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => (gm_res _ y _ hy _).trans (gm_res _ y _ hy _))
  right_inv t := by
    subst h
    exact congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => (gm_res _ y _ hy _).trans (gm_res _ y _ hy _))

theorem le_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (j : Fin 1 ⊕ K → L.ι) :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩

theorem div_le (φ : K → (X ⟶ X)) (ε : K → ℤ) (p : (K → L.ι) × L.ι) :
    (LB.div (LB.LinComb L φ ε) L).U p ≤
      LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => p.2) p.1) := fun _ hy =>
  Set.mem_iInter.2 fun k => by
    rcases k with k | k
    · exact hy.2
    · exact Set.mem_iInter.1 hy.1 k

omit [Fintype K] in
theorem idx_split (j : Fin 1 ⊕ K → L.ι) : ∃ p : (K → L.ι) × L.ι, j = Sum.elim (fun _ => p.2) p.1 :=
  ⟨(j ∘ Sum.inr, j (Sum.inl 0)), funext fun k => by
    rcases k with k | k
    · rw [Subsingleton.elim k 0]; rfl
    · rfl⟩

def divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) : LB.Iso L (LB.LinComb L φ ε) ≃
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) where
  toFun w := ⟨fun j => res (le_div φ ε j) (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩
  invFun v := ⟨fun p => res (div_le φ ε p) (v.s (Sum.elim (fun _ => p.2) p.1))⁻¹⟩
  left_inv w := by
    obtain ⟨s⟩ := w
    refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (div_le φ ε p hy) _).trans (map_inv _ _)
  right_inv v := by
    obtain ⟨s⟩ := v
    refine congrArg LB.Gen.mk (funext fun j => ?_)
    obtain ⟨p, rfl⟩ := idx_split j
    refine unit_ext fun y hy => ?_
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (le_div φ ε _ hy) _).trans (map_inv _ _)

theorem gm_g_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (i j : Fin 1 ⊕ K → L.ι) (y : X)
    (hi : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) i)
    (hj : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) :
    gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j) =
      (gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := by
  have hi' := le_div φ ε i hi
  have hj' := le_div φ ε j hj
  refine (gm_linComb L _ _ (𝟙 _) y i j hi hj).trans (inv_eq_iff_eq_inv.1 (Eq.symm ?_))
  refine (gm_div L (LB.LinComb L φ ε) (𝟙 X) y (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))
    ⟨hi', hj'⟩).trans ?_
  refine (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y _ _ hi'.1 hj'.1) rfl).trans ?_
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
    Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
  rfl

theorem isGen_divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Iso L (LB.LinComb L φ ε)) :
    (divEquiv φ ε w).IsGen ↔ w.IsGen := by
  have hv : ∀ (j : Fin 1 ⊕ K → L.ι) (y : X), y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j →
      gm (𝟙 X) y (LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) ((divEquiv φ ε w).s j) =
        (gm (𝟙 X) y _ (w.s (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := fun j y hy =>
    (gm_res _ y _ hy _).trans (map_inv _ _)
  rw [isGen_iff_gm, isGen_iff_gm]
  constructor
  · intro h p q y hy
    have hp := div_le φ ε p hy.1
    have hq := div_le φ ε q hy.2
    have e := (hv _ y hp).symm.trans ((h _ _ y ⟨hp, hq⟩).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε _ _ y hp hq) (hv _ y hq)))
    exact inv_injective (e.trans (mul_inv _ _).symm)
  · intro h i j y hy
    have e := h (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0)) y ⟨le_div φ ε i hy.1, le_div φ ε j hy.2⟩
    exact (hv i y hy.1).trans (((congrArg (·⁻¹) e).trans (mul_inv _ _)).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε i j y hy.1 hy.2) (hv j y hy.2)).symm)

end General

section Jets

variable {S : Type} [CommRing S] {d : ℕ}

def jetOut (m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin d) m :=
  jetMap (fun p => MvPolynomial.X p.2) fun _ => X_mem_orig _

theorem jetOut_in (m : ℕ) : (jetOut m).comp (jetIn (0 : Fin 1)) = AlgHom.id S (Jet S (Fin d) m) := by
  apply jet_hom_ext
  intro i
  simp [jetOut, jetIn, jetMap_mk]

theorem jetIn_out (m : ℕ) : (jetIn (0 : Fin 1)).comp (jetOut m) = AlgHom.id S (Jet S (Fin 1 × Fin d) m) := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetOut, jetIn, jetMap_mk]

theorem jetCopy_in {n : ℕ} (m : ℕ) (i : Fin n) :
    (jetCopy (S := S) d m i).comp (jetIn (0 : Fin 1)) = jetIn i := by
  apply jet_hom_ext
  intro j
  simp [jetCopy, jetIn, jetMap_mk]

end Jets

section Compare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ : Scheme.{0}} (t : SAB H X₀)

variable {S : Type} [CommRing S] (x : Sp S ⟶ X₀) {d : ℕ}

theorem funOn_eq {B : Type} [CommRing B] (b : B) : funOn b = toΓ B b := rfl

theorem algMap_eq {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] (f : B →ₐ[S] B') :
    algMap x f = homAt x f := rfl

def chartEquiv : JetPts t.G x d ≃ ∀ m, jOG x d m 1 ⟶ t.G where
  toFun j m := jPt t.G x j 1 m 0
  invFun y m := homAt x (jetOut m) ≫ y m
  left_inv j := funext fun m => by
    show homAt x (jetOut m) ≫ homAt x (jetIn (0 : Fin 1)) ≫ j m = j m
    rw [← Category.assoc, homAt_comp, jetOut_in, homAt_id, Category.id_comp]
  right_inv y := funext fun m => by
    show homAt x (jetIn (0 : Fin 1)) ≫ homAt x (jetOut m) ≫ y m = y m
    rw [← Category.assoc, homAt_comp, jetIn_out, homAt_id, Category.id_comp]

theorem jptG_chartEquiv (j : JetPts t.G x d) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t x d (chartEquiv t x j) m i = jPt t.G x j n m i := by
  show homAt x (jetCopy d m i) ≫ homAt x (jetIn (0 : Fin 1)) ≫ j m = homAt x (jetIn i) ≫ j m
  rw [← Category.assoc, homAt_comp, jetCopy_in]

theorem lamφ_eq (j : JetPts t.G x d) (m : ℕ) : lamφ t.G (jPt t.G x j 2 m) =
    cφG t ![jptG t x d (chartEquiv t x j) m (0 : Fin 2), jptG t x d (chartEquiv t x j) m (1 : Fin 2)] := by
  have h : jPt t.G x j 2 m =
      ![jptG t x d (chartEquiv t x j) m (0 : Fin 2), jptG t x d (chartEquiv t x j) m (1 : Fin 2)] := by
    funext i
    fin_cases i
    · exact (jptG_chartEquiv t x j m _).symm
    · exact (jptG_chartEquiv t x j m _).symm
  rw [h]
  rfl

def frameEquiv (j : JetPts t.G x d) :
    FrameFam t.G x t.PP.L j ≃ ∀ m, FrTyG t x d (chartEquiv t x j) m where
  toFun e m := genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m)
  invFun e m := (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).symm (e m)
  left_inv e := funext fun m => (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).symm_apply_apply (e m)
  right_inv e := funext fun m => (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).apply_symm_apply (e m)

theorem frameEquiv_apply (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j) (m : ℕ) :
    frameEquiv t x j e m = genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m) := rfl

variable {t x}

variable {j : JetPts t.G x d} (act : 𝓞 E → Germ.Pt S 1 d) (e : FrameFam t.G x t.PP.L j) (w : PrimIso t)

end Compare

end GlobalTheory.GermSectionCompare
