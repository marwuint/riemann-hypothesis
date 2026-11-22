import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Reg.ChartInhab

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

theorem exists_rigIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    ∃ w, RigIso m w := by
  obtain ⟨w, g, r, -⟩ := m.lin
  exact ⟨w, g, r⟩

theorem exists_comp_rig {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (m' : SABMap t'' t' g) (x : S'' ⟶ S) (hx : x = g ≫ f)
    {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ)}
    (hw : RigIso m w) (hw' : RigIso m' w') :
    ∃ n : SABMap t'' t x, n.φ = m'.φ ≫ m.φ ∧ ∃ w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ t''.G.left) (y : Y) (j : t.PP.L.ι) (i : t'.PP.L.ι) (k : t''.PP.L.ι),
        m.φ (m'.φ (r y)) ∈ t.PP.L.U j → m'.φ (r y) ∈ t'.PP.L.U i → r y ∈ t''.PP.L.U k →
        gw w'' r y j k = gw w (r ≫ m'.φ) y j i * gw w' r y i k := by
  subst hx
  let n : CubeMap t''.G t.G :=
    { F := m'.cm.F ≫ m.cm.F, F3 := m'.cm.F3 ≫ m.cm.F3, e := m'.cm.e ≫ m.cm.e
      e_comm := by rw [← Category.assoc, m'.cm.e_comm, Category.assoc, m.cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, m'.cm.psum_comm, Category.assoc, m.cm.psum_comm, Category.assoc] }
  have hb : n.e = g ≫ f := by
    show m'.cm.e ≫ m.cm.e = g ≫ f
    rw [m'.base, m.base]
  have ha : ∀ a, (t''.act.act a).left ≫ n.F = n.F ≫ (t.act.act a).left := fun a => by
    show _ ≫ m'.cm.F ≫ m.cm.F = (m'.cm.F ≫ m.cm.F) ≫ _
    rw [← Category.assoc, m'.act, Category.assoc, m.act, Category.assoc]
  let N : SABMap t'' t (g ≫ f) := ⟨n, m'.cart.comp m.cart, hb, ha,
    pullCubComp _ _ _ _ _ _ m.cm m'.cm n _ _ _ _ _ _ rfl rfl rfl m.lin m'.lin⟩
  obtain ⟨g1, r1⟩ := (rigIso_iff m w).1 hw
  obtain ⟨g2, r2⟩ := (rigIso_iff m' w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t'.PP.isLB w w' g1 g2 t.PP.isLB t''.PP.isLB
  exact ⟨N, rfl, w'', (rigIso_iff N w'').2 ⟨T.pgen_comp t'.PP.isLB g1 g2,
    T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) r1 r2⟩, T⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Lie

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} (m : SABMap G Xo.univ.t x)

theorem eps_hom : (epsOver V V).hom = spMap (algebraMap V (DualNumber V)) := rfl

def push : (epsOver V V ⟶ G.G) →* (tEps x ⟶ Xo.univ.t.G) := pushHom m.cart (epsOver V V)

theorem push_left (v : epsOver V V ⟶ G.G) : (push m v).left = v.left ≫ m.φ := rfl

end Lie

section Theta

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} (m : SABMap G Xo.univ.t x)

def toGx : G.G.left ⟶ Gx x :=
  (lift (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G)).left

theorem toGx_fst : toGx m ≫ (fst (Over.mk x) Xo.univ.t.G).left = G.G.hom :=
  congrArg (fun q => q.left) (lift_fst (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))

theorem toGx_snd : toGx m ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ :=
  congrArg (fun q => q.left) (lift_snd (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))

theorem exists_inv : ∃ h : Gx x ⟶ G.G.left, h ≫ m.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
    h ≫ G.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ∧ toGx m ≫ h = 𝟙 _ ∧ h ≫ toGx m = 𝟙 _ := by
  have cond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have hφ := m.cart.1.lift_fst _ _ cond
  have hh := m.cart.1.lift_snd _ _ cond
  refine ⟨m.cart.1.lift _ _ cond, hφ, hh, m.cart.1.hom_ext ?_ ?_, FramedBaseChange.pulledGroup_hom_ext _ _ ?_ ?_⟩
  · rw [Category.assoc, hφ, toGx_snd, Category.id_comp]
  · rw [Category.assoc, hh, toGx_fst, Category.id_comp]
  · rw [Category.assoc, toGx_snd, Category.id_comp]; exact hφ
  · rw [Category.assoc, toGx_fst, Category.id_comp]; exact hh

theorem le_toGx (j : Xo.univ.t.PP.L.ι) : m.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ toGx m ⁻¹ᵁ (PPx x).U (fun _ => j) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) (toGx_snd m)).mpr hy

def SecRel (w : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m.φ)) (s : LB.Sec (PPx x)) (τ : LB.Sec G.PP.L) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j k, m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ G.PP.L.U k →
    gs (r ≫ toGx m) z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (τ.f k)

variable {w : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m.φ)}

theorem exists_up (hw : PGen w) (τ : LB.Sec G.PP.L) : ∃ s, SecRel m w s τ := by
  obtain ⟨h, hφ, -, hg, -⟩ := exists_inv m
  obtain ⟨s1, hs1⟩ := thf_secUp hw Xo.univ.t.PP.isLB G.PP.isLB τ
  refine ⟨thfPull1 Xo.univ.t.PP.L h hφ s1, fun Z r z j k h₁ h₂ => ?_⟩
  have mg : (r ≫ toGx m) z ∈ (PPx x).U (fun _ => j) := le_toGx m j h₁
  refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (r ≫ toGx m) z mg _).trans ?_
  rw [Category.assoc, hg, Category.comp_id]
  exact hs1 _ r z (fun _ => j) k (mem_pull.2 h₁) h₂

end Theta

end GlobalTheory.Reg.ChartInhab

namespace GlobalTheory.Reg

end GlobalTheory.Reg
