import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters

noncomputable section

open Module NumberField
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneForm

section GroupAlgebra

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in

def typeSum (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K := ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K)

end GroupAlgebra

section Modules

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V]

omit [CharZero K] in
theorem asAlg_eq_sum (r : Representation K G V) (a : MonoidAlgebra K G) (x : V) :
    r.asAlgebraHom a x = ∑ g : G, a.coeff g • r g x := by
  conv_lhs => rw [eq_sum_single a]
  simp [map_sum, LinearMap.sum_apply]

end Modules

section Coordinates

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_toF {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G)
    (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ LinearMap.range (B.r.asAlgebraHom (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ := by
    intro a φ
    rw [asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
    rfl
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext φ
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩
    have : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
    rw [hV] at this
    obtain ⟨u, hu⟩ := this
    refine ⟨B.S.basis.equivFun.symm u, ?_⟩
    rw [B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun,
      LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨hZ, w, hw⟩
    have : B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]
      refine ⟨B.S.basis.equivFun w, ?_⟩
      rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]
    obtain ⟨u, hu⟩ := this
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact hZ
    obtain ⟨y, hy⟩ := B.exists_zE ℓ Z hu0
    exact ⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  classical
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [CxData.iC, lin_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1 := by
    funext i; by_cases hi : i = k <;> simp [hi]
  rw [this, map_smul, map_smulₛₗ, map_smul]
  rfl

end Coordinates

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m}

def ThetaEquivariant (X : CxData A.fam.amb) (ρ : Representation ℂ G X.EE) : Prop :=
  ∃ ρF : ∀ t, Representation ℂ G (X.FC t),
    (∀ t g x, X.jR t (A.leftGroupActionRight t g x) = ρF t g (X.jR t x)) ∧
    (∀ t g x, X.Θ t (ρF t g x) = ρ g (X.Θ t x)) ∧
    ∀ t g y, LinearMap.adjoint (X.Θ t) (ρ g y) = ρF t g (LinearMap.adjoint (X.Θ t) y)

def OneVector (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, typeSum P ψ χ = (Nat.card P : K)

end Family

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def rowSub (R : RealDat D A Ks) (t : T) : Submodule D.what₂.LL (A.fam.amb.FR t) :=
  (LinearMap.range (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)))).comap
    (Tw.semi (σ' := A.v0.embedding) (twAt D.what₂.embLL A.v0) R.emb0 (R.jX t))

def GoodInduced (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar R.Pg D.R.r D.what₂.embLL fun g => χ (R.eG.symm g)

theorem oneVector_of_whittaker (R : RealDat D A Ks) (F : Face D A) (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector)
    (hlev : R.grp_levels F) (hind : GoodInduced R) : OneVector A.X F.P0 F.ψ0 := by
  classical
  obtain ⟨ψ, hψ, hP, -⟩ := hlev
  intro χ hχ
  have h := hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)
  rw [← hP] at h
  let e : (R.levR F false).H ≃ F.P0 := R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl
  apply D.what₂.embLL.injective
  rw [map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum
  letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_mul]
  rfl

end Concrete

end GlobalTheory.OneForm
