import Mathlib
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.HermLat

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

abbrev rs (R : Type) [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] (S : Submodule K V) :
    Submodule R V := S.restrictScalars R

def perp (H : HermSpace K V) (S : Submodule K V) : Submodule K V :=
  ⨅ x ∈ S, LinearMap.ker (H.B.flip x)

def dual (H : HermSpace K V) (M : Submodule R V) : Submodule R V :=
  rs R (Submodule.span K (M : Set V)) ⊓ Formalism.HermitianLatticesTheory.dual H.B.flip M

def IsIntegralLat (H : HermSpace K V) (M : Submodule R V) : Prop :=
  Formalism.HermitianLatticesTheory.IsIntegralLat H.B.flip M

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.mem_perp_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B y x = 0 := by
  simp [_root_.GlobalTheory.HermLat.perp, Submodule.mem_iInf]

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.mem_dual_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.dual H M ↔
      y ∈ Submodule.span K (M : Set V) ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule R K) := by
  simp only [_root_.GlobalTheory.HermLat.dual, _root_.GlobalTheory.HermLat.rs, Submodule.mem_inf,
    Submodule.restrictScalars_mem, _root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual, LinearMap.flip_apply]

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.isIntegralLat_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsIntegralLat H M ↔ ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule R K) := by
  unfold _root_.GlobalTheory.HermLat.IsIntegralLat _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  simp only [LinearMap.flip_apply]
  exact ⟨fun h x hx y hy => h y hy x hx, fun h x hx y hy => h y hy x hx⟩

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.flip_isSymm (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) : H.B.flip.IsSymm := by
  rw [LinearMap.isSymm_def]
  intro x y
  simp only [LinearMap.flip_apply, starRingEnd_apply]
  exact H.herm y x

def IsLatMod (M : Submodule R V) (S I : Submodule K V) : Prop :=
  (∃ N : Submodule R V, N.FG ∧ M = N ⊔ rs R I) ∧ Submodule.span K (M : Set V) = S

def IsUnimodMod (H : HermSpace K V) (M : Submodule R V) (S I : Submodule K V) : Prop :=
  IsLatMod M S I ∧ dual H M = M

def IsUnimod (H : HermSpace K V) (M : Submodule R V) : Prop := IsUnimodMod H M ⊤ ⊥

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.isLatMod_top_bot_iff (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsLatMod M (⊤ : Submodule K V) ⊥ ↔ Submodule.IsLattice K M := by
  unfold _root_.GlobalTheory.HermLat.IsLatMod
  constructor
  · rintro ⟨⟨N, hN, rfl⟩, hs⟩
    simp only [_root_.GlobalTheory.HermLat.rs, Submodule.restrictScalars_bot, sup_bot_eq] at hs ⊢
    exact { fg := hN, span_eq_top := hs }
  · intro hM
    exact ⟨⟨M, hM.fg, by simp⟩, hM.span_eq_top⟩

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.isUnimod_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsUnimod H M ↔ Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular H.B.flip M := by
  unfold _root_.GlobalTheory.HermLat.IsUnimod _root_.GlobalTheory.HermLat.IsUnimodMod
  rw [_root_.GlobalTheory.HermLat.isLatMod_top_bot_iff]
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular _root_.GlobalTheory.HermLat.dual
  constructor
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM.span_eq_top] at hd
    simpa using hd
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM.span_eq_top]
    simpa using hd

def idx (M M' : Submodule R V) : ℕ := M'.toAddSubgroup.relIndex M.toAddSubgroup

def gidx (M M' : Submodule R V) : ℝ := (idx M M' : ℝ) / (idx M' M : ℝ)

def del (H : HermSpace K V) (M : Submodule R V) : ℝ := Real.sqrt (gidx (dual H M) M)

def smulLat (g : R) (M : Submodule R V) : Submodule R V := M.map (g • (LinearMap.id : V →ₗ[R] V))

def IsModIso (H : HermSpace K V) (g : R) (L' L : Submodule R V) (Γ : Submodule R (V × V)) : Prop :=
  Γ ≤ L'.prod L ∧ (smulLat g L').prod (smulLat g L) ≤ Γ ∧
  (∀ y' ∈ L', ∃ y, (y', y) ∈ Γ) ∧ (∀ y ∈ L, ∃ y', (y', y) ∈ Γ) ∧
  (∀ y, ((0 : V), y) ∈ Γ → y ∈ smulLat g L) ∧ (∀ y', (y', (0 : V)) ∈ Γ → y' ∈ smulLat g L') ∧
  ∀ p ∈ Γ, ∀ q ∈ Γ, ∃ t : R, H.B p.1 q.1 - H.B p.2 q.2 = algebraMap R K (g * t)

def fixLat (Γ : Submodule R (V × V)) : Submodule R V :=
  Γ.comap ((LinearMap.id : V →ₗ[R] V).prod LinearMap.id)

section Term

variable {H : HermSpace K V} {r : ℕ}

def lead (F : FlagD H r) (Λ : Submodule R V) (a : Fin (r + 1)) : Submodule R K :=
  (Λ ⊔ rs R (F.Xa a.val)).comap ((LinearMap.toSpanSingleton K V (F.e a)).restrictScalars R)

def IsFrame (F : FlagD H r) (Λ : Submodule R V) (aa : Fin r → Submodule R K) : Prop :=
  (∀ a : Fin r, lead F Λ a.castSucc = aa a) ∧ lead F Λ (Fin.last r) = 1

def IsAdm (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Prop :=
  ∀ (a : Fin (r + 1)) (t : K) (x' : V), x' ∈ Λ → x' - t • F'.e a ∈ F'.Xa a.val →
    ∃ x ∈ Λ, x - t • F.e a ∈ F.Xa a.val ∧ x - x' ∈ smulLat g Λ

def IsFramed (F F' : FlagD H r) (Λ : Submodule R V) (aa : Fin r → Submodule R K) : Prop :=
  IsUnimod H Λ ∧ IsFrame F Λ aa ∧ IsFrame F' Λ aa

def lamI (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V :=
  (Λ ⊓ rs R (perp H (II F F'))) ⊔ rs R (II F F')

def uPerp (F F' : FlagD H r) : Submodule K V := perp H (F.X ⊔ F'.X)

def wSp (F F' : FlagD H r) : Submodule K V := perp H (V0 F F')

def latL (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V :=
  rs R (uPerp F F') ⊓ (Λ ⊔ rs R F.X)

def flagPairDefinitePartLattice (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := latL F F' Λ ⊓ rs R (wSp F F')

def latA0 (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R F.X) ⊔ rs R (II F F')

def latF (F : FlagD H r) (Λ : Submodule R V) (j : ℕ) : Submodule R V := Λ ⊓ rs R (F.Xa j)

def bOne (F F' : FlagD H r) (Λ : Submodule R V) (j : ℕ) : ℕ :=
  idx (Λ ⊓ rs R F.X) (latF F Λ j ⊔ (Λ ⊓ rs R (II F F')))

def normD (F F' : FlagD H r) (Λ : Submodule R V) (l : ℕ) : ℝ := del H (latF F Λ l ⊔ latF F' Λ l)

def delBar (F F' : FlagD H r) (Λ : Submodule R V) : ℝ := del H (latA0 F F' Λ ⊔ latA0 F' F Λ)

def lamOne (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := lamI F F' Λ ⊓ rs R (uPerp F F')

def cardB (F F' : FlagD H r) (Λ : Submodule R V) : ℕ :=
  idx (lamI F F' Λ ⊓ rs R (F.X ⊔ F'.X)) (latA0 F F' Λ ⊔ latA0 F' F Λ)

def latTh (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := lamOne F F' Λ ⊓ rs R (wSp F F')

def iotaGraph (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Submodule R (V × V) :=
  (flagPairDefinitePartLattice F' F Λ).prod (flagPairDefinitePartLattice F F' Λ) ⊓
    ((Λ.prod Λ ⊓ (smulLat g Λ ⊔ (Λ ⊓ rs R F.X)).comap (LinearMap.snd R V V - LinearMap.fst R V V)) ⊔
      (rs R F'.X).prod (rs R F.X))

def latLa (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Submodule R V := fixLat (iotaGraph F F' Λ g)

end Term

section Genus

def isomGrp (H : HermSpace K V) : Subgroup (V ≃ₗ[K] V) := Formalism.HermitianLatticesTheory.isom H.B.flip

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in

theorem _root_.GlobalTheory.HermLat.mem_isomGrp (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (s : V ≃ₗ[K] V) :
    s ∈ _root_.GlobalTheory.HermLat.isomGrp H ↔ ∀ x y, H.B (s x) (s y) = H.B x y := by
  unfold _root_.GlobalTheory.HermLat.isomGrp _root_.Formalism.HermitianLatticesTheory.isom
  change (∀ x y : V, H.B.flip (s x) (s y) = H.B.flip x y) ↔ _
  simp only [LinearMap.flip_apply]
  exact forall_swap

def imLat (s : V ≃ₗ[K] V) (M : Submodule R V) : Submodule R V := Formalism.HermitianLatticesTheory.gmap s M

def autCard (H : HermSpace K V) (M : Submodule R V) : ENNReal :=
  (Set.encard {s : V ≃ₗ[K] V | s ∈ isomGrp H ∧ imLat s M = M} : ENat)

def InGenus (H : HermSpace K V) (L M : Submodule R V) : Prop := M ∈ Formalism.HermitianLatticesTheory.genus H.B.flip L

end Genus

section Mass

open NumberField

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsTraceDef (H : HermSpace K V) : Prop := ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (H.B x x)

variable [FiniteDimensional K V]

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] in
open NumberField in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
variable [FiniteDimensional K V] in

theorem _root_.GlobalTheory.HermLat.autCard_eq_natCard {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} (hH : _root_.GlobalTheory.HermLat.IsTraceDef H)
    {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M).Finite ∧ 0 < Nat.card (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) ∧
      _root_.GlobalTheory.HermLat.autCard H M = (Nat.card (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) : ENNReal) := by
  have hA := _root_.Formalism.HermitianLatticesTheory.final_autFinite
  unfold _root_.Formalism.HermitianLatticesTheory.AutFinite at hA
  have hfin : (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M).Finite := by
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact hA K V H.B.flip (_root_.GlobalTheory.HermLat.flip_isSymm H) (fun x hx => by simpa using hH x hx) M hM
  have hone : (1 : V ≃ₗ[K] V) ∈ _root_.Formalism.ThetaLiftIndependence.autL H.B.flip M := by
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, _root_.Formalism.ThetaLiftIndependence.LatticeLiftIndependence.gmap_one (K := K) M⟩
  refine ⟨hfin, ?_, ?_⟩
  · have : Finite (_root_.Formalism.ThetaLiftIndependence.autL H.B.flip M) := hfin.to_subtype
    exact Nat.card_pos_iff.2 ⟨⟨⟨1, hone⟩⟩, this⟩
  · have hset : {s : V ≃ₗ[K] V | s ∈ _root_.GlobalTheory.HermLat.isomGrp H ∧
        _root_.GlobalTheory.HermLat.imLat s M = M} = _root_.Formalism.ThetaLiftIndependence.autL H.B.flip M := by
      unfold _root_.Formalism.ThetaLiftIndependence.autL
      rfl
    unfold _root_.GlobalTheory.HermLat.autCard
    rw [hset, ← hfin.cast_ncard_eq, Nat.card_coe_set_eq]
    simp

end Mass

end GlobalTheory.HermLat
