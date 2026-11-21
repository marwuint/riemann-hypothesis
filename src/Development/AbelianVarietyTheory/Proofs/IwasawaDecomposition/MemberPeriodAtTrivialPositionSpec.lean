import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TrueRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {θ : InfF D}

abbrev cuspIn (θ : InfF D) (V : HSp D) : Submodule ℂ (AFs θ V) := (CuspS θ V).comap (AFs θ V).subtype

def cuspEq (θ : InfF D) (V : HSp D) : cuspIn θ V ≃ₗ[ℂ] CuspS θ V := Submodule.comapSubtypeEquivOfLe (CuspS_le θ V)

theorem mem_cuspIn (hθ : IsInfFam θ) {V : HSp D} (F : AFs θ V) : F ∈ cuspIn θ V ↔ IsCuspFun V F.1 :=
  (mem_CuspS (formSub D) hθ).trans ⟨fun h => h.2, fun h => ⟨aut hθ F, h⟩⟩

def trE (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (hk : ∀ φ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V k φ)) :
    Module.End ℂ (AFs θ V) :=
  (LinearMap.funLeft ℂ ℂ fun g => g * k).restrict fun φ hφ => Submodule.subset_span (hk φ (aut hθ ⟨φ, hφ⟩))

theorem trE_cusp (hθ : IsInfFam θ) (V : HSp D) (k hk) (F : AFs θ V) (hF : F ∈ cuspIn θ V) : trE hθ V k hk F ∈ cuspIn θ V := by
  rw [mem_cuspIn hθ] at hF ⊢
  exact (_root_.GlobalTheory.Mem.Th.isCuspFun_closed D V _ _ (aut hθ F).toIsAutFun (aut hθ F).toIsAutFun hF hF).2.2.1 k

def actFin (hθ : IsInfFam θ) (V : HSp D) : GfC V →* Module.End ℂ (AFs θ V) where
  toFun k := trE hθ V k fun φ h => GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic D θ hθ V φ h k k.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_one g))
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_assoc g a b).symm)

open Classical in

def actReal (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Module.End ℂ (AFs θ V) :=
  if h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then trE hθ V (atTau θ V τ g) fun φ hφ => GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace D θ hθ V φ hφ τ g h else 1

theorem actReal_apply (hθ : IsInfFam θ) (V : HSp D) (τ) {g} (h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (F : AFs θ V) (x) :
    (actReal hθ V τ g F).1 x = F.1 (x * atTau θ V τ g) := by
  rw [actReal, dif_pos h]; rfl

theorem mul_mem_UH {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H) (hh : h ∈ Formalism.QuantumDeterminants.UH H) :
    g * h ∈ Formalism.QuantumDeterminants.UH H := by
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]

def chrGrp (D : D7) : Subgroup (IdC D) := (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).1.choose

theorem mem_chrGrp {χ : IdC D} : χ ∈ chrGrp D ↔ IsHC D χ := (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).1.choose_spec χ

def expo (χ : chrGrp D) (τ : D.what₂.Tau) : ℚ := ((mem_chrGrp.1 χ.2).2 τ).choose

theorem expo_spec (χ : chrGrp D) (τ : D.what₂.Tau) : HasInfExp D χ.1 τ (expo χ τ) := ((mem_chrGrp.1 χ.2).2 τ).choose_spec

theorem expo_eq {χ : chrGrp D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ.1 τ a) : expo χ τ = a :=
  (GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).2.1 _ _ _ _ (expo_spec χ τ) h

def ksph (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) :=
  (_root_.GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V S).choose.subgroupOf (GfC V)

theorem mem_ksph {V : HSp D} {S} {g : GfC V} : g ∈ ksph V S ↔ (g : GA D V) ∈ KsphC V S := by
  rw [← (_root_.GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V S).choose_spec.1]; rfl

open Classical in

def transp {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Φ : ThS ψ V W) : ThS ψ W V :=
  if h : IsThetaFun ψ W V (fun x => Φ.1 x.transpose) then ⟨_, mem_ThS.2 h⟩ else 0

theorem transp_apply {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} (h : V.rank ≠ W.rank)
    (Φ : ThS ψ V W) (x : WA V W) : (transp Φ).1 x.transpose = Φ.1 x := by
  rw [transp, dif_pos ((GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 h (mem_ThS.1 Φ.2))]
  rfl

abbrev Trip (D : D7) := Σ (A B : HSp D), A.V →ₗ[D.host.E] B.V

abbrev trip0 (D : D7) : Trip D := ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0⟩

def Bes1 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type := {d : BesDat A B ι // (d.y : GA D B) = 1}

def Is0 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop := (⟨A, B, ι⟩ : Trip D) = trip0 D

def PosT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  (Odd (B.rank - A.rank) → Bes1 A B ι) ⊕ (D.what₂.Word × PLift (Is0 A B ι))

abbrev Ses (θ : InfF D) (A B : HSp D) : Type := AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ

def bes0 (u : D.what₂.Word) : Bes1 (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := ⟨memberBes D u, rfl⟩

def datT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ho : Odd (B.rank - A.rank)) : PosT A B ι → Bes1 A B ι
  | .inl f => f ho
  | .inr x => cast (congrArg (fun t : Trip D => Bes1 t.1 t.2.1 t.2.2) x.2.down.symm) (bes0 x.1)

theorem inr_eq (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) :
    (⟨A, B, ι, .inr x⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), PosT A A' ι) =
      ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0, .inr (x.1, ⟨rfl⟩)⟩ := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  rfl

theorem inr_ne (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) (f) :
    ¬ HEq (.inr x : PosT A B ι) (.inl f : PosT (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)) := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  intro h
  cases eq_of_heq h

section Scale

variable {P Q R : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup R] [Module ℂ R]
  (a : ℂ) (b : P →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (e : R ≃ₗ[ℂ] Q)

theorem ses_add (x x' : P) (y : Q) : a * b (x + x') y = a * b x y + a * b x' y := by simp [mul_add]

theorem ses_smul (c : ℂ) (x : P) (y : Q) : a * b (c • x) y = star c * (a * b x y) := by simp [mul_left_comm]

theorem ses_right (x : P) : IsLinearMap ℂ fun y : R => a * b x (e y) :=
  ⟨fun G G' => by simp [mul_add], fun c G => by simp [mul_left_comm]⟩

end Scale

section Record

variable (hP : PetInt D) (hT : TopInt D) (hB : BesInt D) (hL : LiftAut D) (hθ : IsInfFam θ)
  {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) (Tw : Tow D) (Rc : RecFun D θ ψ)

def per1 (u : D.what₂.Word) : Ses θ (D.sp.X 0) (D.sp.Y 0) :=
  ((GlobalTheory.T.definiteBesselPeriod_sesquilinear D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _))).choose

open Classical in

def perT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : PosT A B ι → Ses θ A B
  | .inl f => if ho : Odd (B.rank - A.rank) then (exists_bes hB hθ hψ (f ho).1).choose else 0
  | .inr x => cast (congrArg (fun t : Trip D => Ses θ t.1 t.2.1) x.2.down.symm) (per1 hθ hψ Rc x.1)

theorem perT_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank))
    (f : Odd (B.rank - A.rank) → Bes1 A B ι) :
    perT hB hθ hψ Rc A B ι (.inl f) = (exists_bes hB hθ hψ (f ho).1).choose := dif_pos ho

theorem perT_inr (u : D.what₂.Word) :
    perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) = per1 hθ hψ Rc u := rfl

theorem clause_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank)) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (f : Odd (B.rank - A.rank) → Bes1 A B ι) {μ 𝓕} (hμ : IsVolPair D A μ 𝓕)
    {s : GA D A → GA D B} (hs : ∀ h, EmbRel B A ι (s h) h) (φ : AFs θ A) (F : cuspIn θ B) (hφ : IsAniso A ∨ φ ∈ cuspIn θ A) :
    GlobalTheory.BesselCompare.ClauseFlag ψ (f ho).1 μ 𝓕 s φ.1 F.1.1 (Rc.petC A)
      ((Rc.petC A : ℂ) * perT hB hθ hψ Rc A B ι (.inl f) φ (cuspEq θ B F)) := by
  intro ν 𝓝 h1 h2 h3
  have h := (exists_bes hB hθ hψ (f ho).1).choose_spec hA hι μ 𝓕 hμ s hs φ (cuspEq θ B F) hφ ν 𝓝 h1 h2 h3
  rw [perT_inl hB hθ hψ Rc ho f, h, one_mul]
  rfl

theorem memberPeriodAtTrivialPosition_spec (u : D.what₂.Word) {μ 𝓕} (hμ : IsVolPair D (D.sp.X 0) μ 𝓕) {ν 𝓝} (hν : (Rc.per1.dat u).bes.IsUnitPair ν 𝓝)
    {s : GA D (D.sp.X 0) → GA D (D.sp.Y 0)} (hs : ∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h)
    (φ : AFs θ (D.sp.X 0)) (F : cuspIn θ (D.sp.Y 0)) :
    (Rc.petC (D.sp.X 0) : ℂ) * perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) φ (cuspEq θ _ F) =
      (Rc.petC (D.sp.X 0) : ℂ) * (Rc.per1.dat u).period ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1.1 := by
  rw [perT_inr, per1, ← ((GlobalTheory.T.definiteBesselPeriod_sesquilinear D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0)
    (D.sp.X_def 0 (Nat.zero_le _))).choose_spec μ 𝓕 hμ ν 𝓝 hν s hs φ (cuspEq θ _ F)]
  rfl

theorem adm {V W : HSp D} (χ χ' : chrGrp D) (h : V.rank ≠ W.rank) (h1 : ResEta D χ.1 V.rank) (h2 : ResEta D χ'.1 W.rank) :
    admitted V W χ.1 χ'.1 := ⟨h, mem_chrGrp.1 χ.2, mem_chrGrp.1 χ'.2, h1, h2⟩

theorem range_ThS (V W : HSp D) : Set.range (ThS ψ V W).subtype = {f | IsThetaFun ψ V W f} :=
  Set.ext fun f => ⟨fun ⟨x, hx⟩ => hx ▸ mem_ThS.1 x.2, fun h => ⟨⟨f, mem_ThS.2 h⟩, rfl⟩⟩

end Record

end GlobalTheory.Mem.TrueRecord

end
