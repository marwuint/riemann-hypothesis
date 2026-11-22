import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]

abbrev rs (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

def cst (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) : R →+* Γ(X, W) :=
  (rs X le_top).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def pw (H : LB X) (t : ℤ) : LB X := ⟨H.ι, H.U, fun i j => H.g i j ^ t⟩

def tw (M H : LB X) (t : ℤ) : LB X := LB.div M (pw H (-t))

def VeryAmpleBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) {m : ℕ} (s : Fin (m + 1) → LB.Sec H) : Prop :=
  (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus (s i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r)

def IsProjBy (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ H : LB X, H.IsLB ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec H), VeryAmpleBy f H s

def FirstCohomologyVanishes (M : LB X) : Prop :=
  ∀ (I : Type) (V : I → X.Opens) (c : I → M.ι) (hV : ∀ a, V a ≤ M.U (c a)), ⨆ a, V a = ⊤ →
    ∀ φ : ∀ a b, Γ(X, V a ⊓ V b),
      (∀ a b d, rs X (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b) (φ a b) +
          rs X (le_inf ((inf_le_left.trans inf_le_left).trans (hV a)) ((inf_le_left.trans inf_le_right).trans (hV b)) :
            V a ⊓ V b ⊓ V d ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val *
          rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d) (φ b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d) (φ a d)) →
      ∃ ψ : ∀ a, Γ(X, V a), ∀ a b, φ a b = rs X inf_le_left (ψ a) -
        rs X (inf_le_inf (hV a) (hV b) : V a ⊓ V b ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val * rs X inf_le_right (ψ b)

theorem le_pull (M : LB X) (π : X' ⟶ X) {W : X.Opens} {i : M.ι} (h : W ≤ M.U i) :
    π ⁻¹ᵁ W ≤ (M.pull π).U (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

structure Perf (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) where

  a : ℕ

  b : ℕ

  c : ℕ

  D₀ : Matrix (Fin b) (Fin a) R

  D₁ : Matrix (Fin c) (Fin b) R

  comp : D₁ * D₀ = 0

  I : Type

  W : I → X.Opens

  ch : I → M.ι

  le : ∀ i, W i ≤ M.U (ch i)

  cover : ⨆ i, W i = ⊤

  u : Fin a → ∀ i, Γ(X, W i)

  sec : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')),
    IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
    ∃ E : {v : Fin a → R' // (D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π),
      ∀ v i, rs X' (le_pull M π (le i)) ((E v).f (fun _ => ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ W i) (v.1 k) * (π.app (W i)).hom (u k i)

  exact : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')),
    IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → FirstCohomologyVanishes (M.pull π) →
    ∀ w : Fin b → R', (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w

def Triv (M : LB X) : Prop := ∃ t : LB.Gen M, t.IsGen

theorem rs_rs {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    rs X h₂ (rs X h₁ x) = rs X (h₂.trans h₁) x := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) x = _
  rw [← Functor.map_comp]
  rfl

theorem rs_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) : rs X h x = x := by
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom x = x
  rw [X.presheaf.map_id]
  rfl

theorem rs_cst (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    rs X h (cst f U r) = cst f V r :=
  rs_rs le_top h _

theorem isLB_pw {H : LB X} (hH : H.IsLB) (t : ℤ) : (pw H t).IsLB where
  cover := hH.cover
  g_self := fun i => by
    have h := congrArg (· ^ t) (hH.g_self i)
    simp only [one_zpow, ← map_zpow] at h
    exact h
  cocycle := fun i j k => by
    have h := congrArg (· ^ t) (hH.cocycle i j k)
    simp only [mul_zpow, ← map_zpow] at h
    exact h

theorem isLB_tw {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) (t : ℤ) : (tw M H t).IsLB :=
  LB.isLB_div hM (isLB_pw hH (-t))

theorem tw_g (M H : LB X) (t : ℤ) (p q : M.ι × H.ι) :
    (tw M H t).g p q =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2) ^ t := by
  change _ * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹ = _
  rw [map_zpow, zpow_neg, inv_inv]
  rfl

theorem cst_bijective (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] {W : X.Opens} (hW : W = ⊤) :
    Function.Bijective (cst f W) := by
  subst hW
  have h₁ : Function.Bijective (rs X (le_top : (⊤ : X.Opens) ≤ ⊤)) := by
    have : ⇑(rs X (le_top : (⊤ : X.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₂ : Function.Bijective f.appTop.hom := ConcreteCategory.bijective_of_isIso (f.app ⊤)
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  exact h₁.comp (h₂.comp h₃)

theorem triv_trivLB (X : Scheme.{0}) : Triv (Inh.trivLB X) :=
  ⟨⟨fun _ => 1⟩, fun _ _ => by
    change res _ 1 = 1 * res _ 1
    rw [map_one, map_one]
    exact (_root_.mul_one _).symm⟩

def oneSec (X : Scheme.{0}) : LB.Sec (Inh.trivLB X) where
  f := fun _ => 1
  compat := fun _ _ => by
    rw [map_one, map_one, _root_.mul_one]
    rfl

theorem nonzeroLocus_oneSec (X : Scheme.{0}) : nonzeroLocus (oneSec X) = ⊤ := by
  apply top_unique
  intro x _
  simp only [nonzeroLocus, oneSec, Scheme.basicOpen_one]
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩

theorem veryAmpleBy_oneSec (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    VeryAmpleBy f (Inh.trivLB X) (m := 0) (fun _ => oneSec X) := by
  refine ⟨by simp only [iSup_const]; exact nonzeroLocus_oneSec X, fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [nonzeroLocus_oneSec]
    have : IsAffine X := isAffine_of_isAffineHom f
    exact isAffineOpen_top X
  · intro j k
    rw [map_one, _root_.one_mul]
  · intro p
    obtain ⟨a, rfl⟩ := (cst_bijective f (nonzeroLocus_oneSec X)).2 p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem isProjBy_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] : IsProjBy f :=
  ⟨Inh.trivLB X, Inh.trivLB_isLB X, 0, fun _ => oneSec X, veryAmpleBy_oneSec f⟩

theorem isProjBy_id (R : Type) [CommRing R] : IsProjBy (𝟙 (Spec (CommRingCat.of R))) :=
  isProjBy_of_isIso _

end GlobalTheory.AbLaw
