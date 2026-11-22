import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable (F : Type) [Field F] [NumberField F] [IsCMField F]

structure Datum where
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  w : 𝓞 F
  w_add : w + bar w = 1
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 F) La]
  fin : Module.Finite (𝓞 F) La
  proj : Module.Projective (𝓞 F) La
  n : ℕ
  rank : Module.finrank (𝓞 F) La = n
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 F) x y, EF (a • x) y = EF x (bar a • y)
  sig : (F →+* ℂ) → ℕ
  sig_conj : ∀ τ, sig τ + sig ((starRingEnd ℂ).comp τ) = n
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      J ∘ₗ A = A ∘ₗ J ∧
      LinearMap.trace ℝ _ A = 2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).re ∧
      LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * (∑ τ : F →+* ℂ, (sig τ : ℂ) * τ (a : F)).im

attribute [instance] Datum.acg Datum.mod

variable {F}

def Datum.reflex (D : Datum F) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun a : F => ∑ τ : F →+* ℂ, (D.sig τ : ℂ) * τ a)

def Datum.OEp (D : Datum F) (p : ℕ) : Subring ℂ :=
  Subring.closure ({x | x ∈ D.reflex ∧ IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

def ZbarP (p : ℕ) : Subring ℂ :=
  Subring.closure ({x : ℂ | IsIntegral ℤ x} ∪ {x | ∃ m : ℕ, m.Coprime p ∧ x = (m : ℂ)⁻¹})

theorem OEp_le (D : Datum F) (p : ℕ) : D.OEp p ≤ ZbarP p :=
  Subring.closure_mono (Set.union_subset_union (fun _ hx => hx.2) le_rfl)

def embP (p : ℕ) (τ : F →+* ℂ) (a : 𝓞 F) : ZbarP p :=
  ⟨τ (a : F), Subring.subset_closure (Or.inl ((NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom))⟩

variable {S : Scheme.{0}}

open Classical in

def DetCondP (D : Datum F) (p : ℕ) {k : Type} [Field k] {G : Over S} [GrpObj G] (act : OAct (𝓞 F) G)
    (x : Sp k ⟶ S) (β : D.OEp p →+* k) : Prop :=
  ∃ β' : ZbarP p →+* k, (∀ y : D.OEp p, β' (Subring.inclusion (OEp_le D p) y) = β y) ∧
    ∀ σ : 𝓞 F →+* k, LieMult act x σ
      (∑ τ ∈ (Finset.univ.filter fun τ : F →+* ℂ => ∀ a, β' (embP p τ a) = σ a), D.sig τ)

structure TateIsoP (D : Datum F) (p : ℕ) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 F → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n a b, ev n (a + b) = ev n a * ev n b
  lin : ∀ n (c : 𝓞 F) a, ev n (c • a) = act c (ev n a)
  ker : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = 1 ↔ ∃ b, a = n • b
  onto : ∀ n, 0 < n → n.Coprime p → ∀ x, x ^ n = 1 ↔ ∃ a, ev n a = x
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ a, ev (n * m) a ^ m = ev n a
  isom : ∀ n, 0 < n → n.Coprime p → ∀ a b, e n (ev n a) (ev n b) (ζ n ^ D.EF a b)

structure Obj (D : Datum F) (p N : ℕ) (s : S ⟶ Sp (D.OEp p)) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OAct (𝓞 F) A
  PP : RigLB A
  cub : CubicalStr A PP
  sym : PP.IsSymmetric
  adj : ∀ a, LBIso (cubeLB A ![fst A A ≫ act.act a, snd A A] PP.L)
    (cubeLB A ![fst A A, snd A A ≫ act.act (D.bar a)] PP.L)
  prim : LBIso PP.L (cubeLB A ![𝟙 A, act.act D.w] PP.L)
  ample : Out.RelAmple A PP.L
  ktriv : Out.KTriv A PP.L
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ a c, eta (a + c) = eta a * eta c
  eta_ker : ∀ a, eta (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : D.OEp p →+* k), x ≫ s = spMap β →
    DetCondP D p act x β ∧
    ∃ I : TateIsoP D p k (Over.mk x ⟶ A) (fun a g => g ≫ act.act a)
        (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)),
      ∀ a, toUnit _ ≫ eta a = I.ev N a

attribute [instance] Obj.grp Obj.comm

structure ObjMap {D : Datum F} {p N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp (D.OEp p)} {s : S ⟶ Sp (D.OEp p)}
    (o' : Obj D p N s') (o : Obj D p N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  cart : IsGrpPullback o'.A o.A f φ
  act : ∀ a, (o'.act.act a).left ≫ φ = φ ≫ (o.act.act a).left
  pol : LBIso o'.PP.L (o.PP.L.pull φ)
  eta : ∀ a, (o'.eta a).left ≫ φ = f ≫ (o.eta a).left

def Datum.dim (D : Datum F) : ℕ := (∑ τ : F →+* ℂ, D.sig τ * (D.n - D.sig τ)) / 2

structure IntModel (D : Datum F) (p N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (D.OEp p)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D p N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (D.OEp p)), IsReduced S → ∀ o : Obj D p N s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D p N (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x

def Good (F : Type) [Field F] [NumberField F] (p N : ℕ) : Prop :=
  p.Prime ∧ ¬ (p : ℤ) ∣ NumberField.discr F ∧ 3 ≤ N ∧ N.Coprime p

def ObjMap.refl {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  cart := by
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
    let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
    have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
    rw [e₁, e₂, ← MonObj.comp_mul]
    simp [j]
  act a := by simp
  pol := (GlobalTheory.PolBaseChange.lbIso_refl o.PP.isLB).chartPull (Geo.Tor.chartPullId _)
    (Geo.Tor.chartPullPull _ _ _ rfl)
  eta a := by simp

end GlobalTheory.UPel
