import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

namespace Formalism.L2.SG.CntLocal

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical ValuativeRel

set_option linter.dupNamespace false

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

structure LocSp (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Type 1 where
  V : PlF D → Type
  [acg : ∀ p, AddCommGroup (V p)]
  [mod : ∀ p, Module (D.s.atP p).Ep (V p)]
  H : ∀ p, Loc.HermSp (M p) (V p)
  rank : ∀ p, Module.finrank (D.s.atP p).Ep (V p) = D.R.r
  bc : ∀ p, (VS D).V →+ V p
  bc_smul : ∀ p (a : D.host.E) (x : (VS D).V), bc p (a • x) = (D.s.atP p).ιE a • bc p x
  bc_span : ∀ p, Submodule.span (D.s.atP p).Ep (Set.range (bc p)) = ⊤
  bc_form : ∀ p (x y : (VS D).V), (H p).h (bc p x) (bc p y) = (D.s.atP p).ιE (brS (VS D) x y)

attribute [instance] LocSp.acg LocSp.mod

variable {D}

abbrev Tn (u : D.what₂.Word) : D.host.E := (((D.mem u).A.T : ℕ) : D.host.E)

abbrev MatZ (D : Formalism.BasicNotions.D7) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E

def GZ (T T' : D.host.E) (Z : MatZ D) : D.host.E :=
  leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) -
    T * T' * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))

def sqrtAbsNormOfScaledGram (T T' : D.host.E) (Z : MatZ D) : ℝ :=
  Real.sqrt |((Algebra.norm ℚ (GZ T T' Z / ((Lat.gS D : D.host.E) ^ D.R.m)) : ℚ) : ℝ)|

def Ga (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.fromBlocks
    (Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0) Z
    Z.conjTranspose
    (Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0)

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (frFac δ p) (frFac δ p)

def ZhatLoc (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (Z : MatZ D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) * (D.s.atP p).ιE (Z a b)

def GaLoc (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => phi δ p b * (M p).L.cj (phi δ p a) * (D.s.atP p).ιE (Ga T T' Z a b)

def GaPlus (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  match (M p).split with
  | none => GaLoc M δ p T T' Z
  | some g =>
    let qi : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)
    let A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
      Matrix.fromBlocks 1 (-qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
        (qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))
    (A.map (M p).L.cj).transpose * GaLoc M δ p T T' Z * A

def lattice₂ (L : LocSp D M) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (M p).L.O (L.V p) :=
  Submodule.span (M p).L.O (L.bc p '' (Λ : Set (VS D).V))

def densP (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp])
    (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : ℝ :=
  (L.H p).dens (ϖ p) (lattice₂ L p (VS D).L0) (GaPlus M δ p T T' Z)

def ZZP (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (p : PlF D) (Z : MatZ D) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z) (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp)
    (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp)

def N0 {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ NLam Λ (lf D F0) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def EZ {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : MatZ D) : Set (LFlag (VS D) D.R.rS T') :=
  {F' | IsTerm Λ (gS D) (lf D F0) F' ∧ AdmWit Λ (gS D) (lf D F0) F' 1 ∧ IsGeneric Λ (gS D) (lf D F0) F' ∧
    FrameOK D Λ F' ∧ ZhatL (lf D F0) F' = Z}

def NilradicalFlagMoved {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F' F'' : LFlag (VS D) D.R.rS T') : Prop :=
  ∃ n ∈ N0 F0 Λ, (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def cntE {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : MatZ D) : ENat :=
  Set.encard {O : Set (LFlag (VS D) D.R.rS T') | ∃ F' ∈ EZ T' F0 Λ Z,
    O = {F'' | F'' ∈ EZ T' F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}}

def nu {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (Z : MatZ D) : ℝ :=
  (∑ Λ ∈ what₂, wRow D F0 Λ * ((cntE T' F0 Λ Z).toNat : ℝ)) / ∑ Λ ∈ what₂, wRow D F0 Λ

def RowsOf (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ IsRowReps D F0 what₂ ∧ what₂.Nonempty

def Formula (δ : ∀ p : PlF D, (D.s.atP p).Fp) (L : LocSp D M) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (c : ℝ) : Prop :=
  0 < c ∧ ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ Z : MatZ D,
    (∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤) ∧
    (TotPos (GZ (Tn u) (Tn u') Z) →
      Multipliable (densP L δ ϖ (Tn u) (Tn u') Z) ∧
      nu (Tn u') F0 what₂ Z =
        c * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) * ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p)

def NotInt (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ Z : MatZ D, (∃ p a b, ZZP (M := M) δ u u' p Z a b ∉ (M p).R) → nu (Tn u') F0 what₂ Z = 0

section
variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Formalism.MainNotions.S.Loc.HermSp M V)

def hL (y : V) : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h (∑ i ∈ s, x i) y = ∑ i ∈ s, H.h (x i) y := map_sum (hL H y) x s

end

theorem gz_eq (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Gval F F' = GZ T T' (ZhatL F F') := rfl

theorem ga_gram (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    Ga T T' (Zhat F F') a b = brS (VS D) (Sum.elim F.fvec F'.fvec b) (Sum.elim F.fvec F'.fvec a) := by
  have hs : ∀ x y : (VS D).V, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have key : ∀ {S : ℕ} {U : D.host.E} (G : FlagG (VS D) D.R.rS U) (a b : Fin (D.R.rS + 1)),
      (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -U else 0 := by
    intro S U G a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast j =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← hs, G.z_orth j]; simp
    | cast i =>
      induction b using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth]
      | cast j => simp [FlagG.fvec, G.e_iso]
  rcases a with a | a <;> rcases b with b | b
  · simp only [Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, Sum.elim_inl, brS]
    rw [key (S := 0) F a b]
  · rfl
  · simp only [Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Zhat, brS, Sum.elim_inl, Sum.elim_inr]
    exact hs _ _
  · simp only [Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Sum.elim_inr, brS]
    rw [key (S := 0) F' a b]

end Formalism.L2.SG.CntLocal
