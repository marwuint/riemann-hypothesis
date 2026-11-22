import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

variable (a) in

theorem PiSys.isGalois_field (he : e ∣ l ^ a - 1) : IsGalois ℚ_[l] ↥(ϖ.field a).1 := by
  have : Normal ℚ_[l] ↥(ϖ.field a).1 := by
    refine IntermediateField.normal_iff_forall_map_le'.2 fun g => ?_
    rw [IntermediateField.map_le_iff_le_comap]
    refine sup_le (IntermediateField.adjoin_le_iff.2 fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · exact ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _
        (show g x ^ l ^ a = g x by rw [← map_pow, show x ^ l ^ a = x from hx]))
    · rintro _ rfl
      have h1 : (g (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
        rw [div_pow, ← map_pow, ϖ.seq_zero, map_neg, map_natCast,
          div_self (neg_ne_zero.2 (Nat.cast_ne_zero.2 hl.out.ne_zero))]
      obtain ⟨k, hk⟩ := he
      have h2 : g (ϖ.seq 0) / ϖ.seq 0 ∈ Kunr l a := IntermediateField.subset_adjoin _ _
        (show _ ^ l ^ a = _ by
          rw [← Nat.sub_add_cancel (one_lt_pow_l l a).le, pow_succ, hk, pow_mul, h1, one_pow, one_mul])
      have h3 := mul_mem (ϖ.Kunr_le_field a h2) (ϖ.pi_mem_field a)
      rwa [div_mul_cancel₀ _ (ϖ.seq_ne_zero 0)] at h3
  exact {}

section Real

variable (P : PhiMod O K l e a ι)

def frobMat : Matrix ι ι (OW l O) :=
  (Matrix.of fun i j τ => (P.mat τ : Matrix ι ι (invE l e (A O K))) i j).map (ϖ.iW t K)

def frobMatInv : Matrix ι ι (OW l O) :=
  (Matrix.of fun i j τ => (((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) : Matrix ι ι (invE l e (A O K))) i j).map
    (ϖ.iW t K)

theorem frobMat_mul_inv : frobMat t ϖ P * frobMatInv t ϖ P = 1 := by
  rw [frobMat, frobMatInv, ← Matrix.map_mul, ← Matrix.map_one (ϖ.iW t K) (map_zero _) (map_one _)]
  congr 1
  ext1 i j
  ext1 τ
  have h := congrFun₂ (P.mat τ).mul_inv i j
  simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply, Matrix.one_apply,
    apply_ite (fun f : ZMod a → invE l e (A O K) => f τ), Pi.one_apply, Pi.zero_apply] using h

theorem frobMatInv_mul : frobMatInv t ϖ P * frobMat t ϖ P = 1 := mul_eq_one_comm.1 (frobMat_mul_inv t ϖ P)

def phiW : (ι → OW l O) →ₗ[O] (ι → OW l O) :=
  ((frobMat t ϖ P).mulVecLin.restrictScalars O).comp ((frobOW l O).toLinearMap.compLeft ι)

theorem phiW_apply (v : ι → OW l O) : phiW t ϖ P v = frobMat t ϖ P *ᵥ fun i => frobOW l O (v i) := rfl

theorem phiW_smul (r : OW l O) (v : ι → OW l O) : phiW t ϖ P (r • v) = frobOW l O r • phiW t ϖ P v := by
  rw [phiW_apply, phiW_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  exact map_mul _ _ _

def Treal : Submodule O (ι → OW l O) := LinearMap.eqLocus (phiW t ϖ P) LinearMap.id

variable {t ϖ P} in

theorem mem_Treal {v : ι → OW l O} : v ∈ Treal t ϖ P ↔ phiW t ϖ P v = v := Iff.rfl

abbrev ME : Submodule (invE l e (A O K)) (Vec K a ι) := P.Mext (invE l e (A O K))

variable {P} in
omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem mem_ME_of_mem_M {v : Vec K a ι} (hv : v ∈ P.M) : v ∈ ME P :=
  mem_tot.2 fun τ i => le_away _ _ (mem_tot.1 hv τ i)

variable {P} in
omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem mem_ME_of_mem_L {v : Vec K a ι} (hv : v ∈ P.L) : v ∈ ME P :=
  mem_tot.2 fun τ i => by
    obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 hv τ)
    rw [h]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (P.mx_mem τ i j) (le_away _ _ (hm j))

omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

def coordM (B : Subalgebra O K⟦X⟧) : P.Mext B →ₗ[O] (ι → ZMod a → B) where
  toFun v i τ := ⟨v.1 τ i, mem_tot.1 v.2 τ i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toW : ME P →ₗ[O] (ι → OW l O) := ((ϖ.iW t K).toLinearMap.compLeft ι).comp (coordM P _)

theorem toW_apply (v : ME P) (i : ι) :
    toW t ϖ P v i = ϖ.iW t K fun τ => ⟨v.1 τ i, mem_tot.1 v.2 τ i⟩ := rfl

theorem toW_injective : Function.Injective (toW t ϖ P) := fun _ _ h =>
  Subtype.ext (funext fun τ => funext fun i =>
    congrArg Subtype.val (congrFun (ϖ.iW_injective t K (congrFun h i)) τ))

theorem toW_smul (f : ZMod a → invE l e (A O K)) (v w : ME P) (h : ∀ τ, w.1 τ = (f τ : K⟦X⟧) • v.1 τ) :
    toW t ϖ P w = ϖ.iW t K f • toW t ϖ P v := by
  ext1 i
  rw [Pi.smul_apply, toW_apply, toW_apply, smul_eq_mul, ← map_mul]
  exact congrArg _ (funext fun τ => Subtype.ext (congrFun (h τ) i))

theorem toW_of_mx (v : ME P) (m : ι → ZMod a → A O K) (h : ∀ τ, v.1 τ = P.mx τ *ᵥ fun j => m j τ) :
    toW t ϖ P v = frobMat t ϖ P *ᵥ fun j => inclO l O (ϖ.iTot t K (m j)) := by
  ext1 i
  simp only [← ϖ.iW_of_mem t K]
  change _ = ∑ j, ϖ.iW t K _ * ϖ.iW t K _
  simp only [← map_mul]
  rw [← map_sum, toW_apply]
  refine congrArg _ (funext fun τ => Subtype.ext ?_)
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
  exact congrFun (h τ) i

theorem toW_phi {v : Vec K a ι} (hv : v ∈ P.M) :
    toW t ϖ P ⟨P.phi v, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ = phiW t ϖ P (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩) := by
  rw [toW_of_mx t ϖ P _ (fun j => frobAc l fun τ => ⟨v τ j, mem_tot.1 hv τ j⟩) fun τ => rfl, phiW_apply]
  congr 1
  ext1 j
  rw [PiSys.iTot_frob, ← frobOW_inclO, ← ϖ.iW_of_mem t K]
  rfl

variable (l O ι) in

def inclV : (ι → OA l O) →ₗ[O] (ι → OW l O) := (inclO l O).toLinearMap.compLeft ι

def MA (_ : PhiMod O K l e a ι) : Submodule O (ι → OW l O) := LinearMap.range (inclV l O ι)

def inclL : (ι → OA l O) →ₗ[O] (ι → OW l O) :=
  ((frobMat t ϖ P).mulVecLin.restrictScalars O).comp (inclV l O ι)

theorem inclL_apply (c : ι → OA l O) : inclL t ϖ P c = frobMat t ϖ P *ᵥ fun i => inclO l O (c i) := rfl

theorem inclL_injective : Function.Injective (inclL t ϖ P) := fun c c' h => by
  have h1 := congrArg (frobMatInv t ϖ P *ᵥ ·) h
  simp only [inclL_apply, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec] at h1
  exact funext fun i => inclO_injective (congrFun h1 i)

def LA : Submodule O (ι → OW l O) := LinearMap.range (inclL t ϖ P)

theorem toW_mem_MA {v : Vec K a ι} (hv : v ∈ P.M) : toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩ ∈ MA P :=
  ⟨fun i => ϖ.iTot t K fun τ => ⟨v τ i, mem_tot.1 hv τ i⟩, funext fun _ => (ϖ.iW_of_mem t K _).symm⟩

theorem toW_mem_LA {v : Vec K a ι} (hv : v ∈ P.L) : toW t ϖ P ⟨v, mem_ME_of_mem_L hv⟩ ∈ LA t ϖ P := by
  choose m hm h using fun τ => P.mem_extc.1 (mem_tot.1 hv τ)
  exact ⟨_, (toW_of_mx t ϖ P _ (fun j τ => ⟨m τ j, hm τ j⟩) h).symm⟩

omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

def coordL (B : Subalgebra O K⟦X⟧) : P.ext B →ₗ[O] (ι → ZMod a → B) where
  toFun v i τ := ⟨(P.mxInv τ *ᵥ v.1 τ) i, P.mem_extc_iff.1 (mem_tot.1 v.2 τ) i⟩
  map_add' v w := funext fun i => funext fun τ => Subtype.ext (congrFun (Matrix.mulVec_add (P.mxInv τ) (v.1 τ) (w.1 τ)) i)
  map_smul' c v := funext fun i => funext fun τ => Subtype.ext (congrFun (Matrix.mulVec_smul (P.mxInv τ) c (v.1 τ)) i)

omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem mx_mulVec_coordL (B : Subalgebra O K⟦X⟧) (v : P.ext B) (τ : ZMod a) :
    (P.mx τ *ᵥ fun i => (coordL P B v i τ : K⟦X⟧)) = v.1 τ := by
  change P.mx τ *ᵥ (P.mxInv τ *ᵥ v.1 τ) = _
  rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]

def toCris : P.MM →ₗ[O] (ι → OCr l O) := ((ϖ.iC t K).toLinearMap.compLeft ι).comp (coordL P (S O K e))

def toBcris : P.MMl →ₗ[O] (ι → OB l O) :=
  ((ϖ.iB t K).toLinearMap.compLeft ι).comp (coordL P (invL l (S O K e)))

theorem toCris_apply (m : P.MM) (i : ι) : toCris t ϖ P m i = ϖ.iC t K (coordL P (S O K e) m i) := rfl

theorem toBcris_apply (m : P.MMl) (i : ι) :
    toBcris t ϖ P m i = ϖ.iB t K (coordL P (invL l (S O K e)) m i) := rfl

theorem toW_toCris_of_mem_L {v : Vec K a ι} (hv : v ∈ P.L) (hv' : v ∈ P.MM) :
    toW t ϖ P ⟨v, mem_ME_of_mem_L hv⟩ = inclL t ϖ P (fun i => ϖ.iTot t K (coordL P _ ⟨v, hv⟩ i)) ∧
      toCris t ϖ P ⟨v, hv'⟩ = fun i => toOCr l O (ϖ.iTot t K (coordL P _ ⟨v, hv⟩ i)) :=
  ⟨toW_of_mx t ϖ P _ _ fun τ => (mx_mulVec_coordL P _ ⟨v, hv⟩ τ).symm,
    funext fun i => ϖ.iC_of_mem t K (coordL P _ ⟨v, hv⟩ i)⟩

end Real

section Hom

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {R : PhiMod O K l e a μ}

def homMat (F : BK.Hom P Q) : Matrix κ ι (OA l O) :=
  Matrix.of fun i j => ϖ.iTot t K fun τ => ⟨F.mat τ i j, F.mem τ i j⟩

def homW (F : BK.Hom P Q) : (ι → OW l O) →ₗ[OW l O] (κ → OW l O) :=
  ((homMat t ϖ F).map (inclO l O)).mulVecLin

theorem homW_apply (F : BK.Hom P Q) (v : ι → OW l O) :
    homW t ϖ F v = (homMat t ϖ F).map (inclO l O) *ᵥ v := rfl

theorem homW_toW (F : BK.Hom P Q) (v : ME P) :
    homW t ϖ F (toW t ϖ P v) = toW t ϖ Q ⟨F.app v, F.app_mem_Mext (le_away _ _) v.2⟩ := by
  ext1 i
  change ∑ j, inclO l O (ϖ.iTot t K _) * ϖ.iW t K _ = _
  simp only [← ϖ.iW_of_mem t K, ← map_mul]
  rw [← map_sum, toW_apply]
  refine congrArg _ (funext fun τ => Subtype.ext ?_)
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rfl

theorem homMat_mul_frobMat (F : BK.Hom P Q) : (homMat t ϖ F).map (inclO l O) * frobMat t ϖ P =
    frobMat t ϖ Q * ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) := by
  ext1 i j
  change ∑ k, inclO l O (ϖ.iTot t K _) * ϖ.iW t K _ =
    ∑ k, ϖ.iW t K _ * frobOW l O (inclO l O (ϖ.iTot t K _))
  simp only [frobOW_inclO, ← PiSys.iTot_frob]
  simp only [← ϖ.iW_of_mem t K, ← map_mul]
  rw [← map_sum, ← map_sum]
  refine congrArg _ (funext fun τ => Subtype.ext ?_)
  rw [Finset.sum_apply, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
  exact congrFun₂ (F.comm τ) i j

theorem homW_phiW (F : BK.Hom P Q) (v : ι → OW l O) :
    homW t ϖ F (phiW t ϖ P v) = phiW t ϖ Q (homW t ϖ F v) := by
  rw [homW_apply, phiW_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, phiW_apply]
  congr 1
  ext1 i
  exact (RingHom.map_mulVec (frobOW l O).toRingHom _ _ i).symm

def homT (F : BK.Hom P Q) : Treal t ϖ P →ₗ[O] Treal t ϖ Q :=
  ((homW t ϖ F).restrictScalars O).restrict fun v hv =>
    mem_Treal.2 ((homW_phiW t ϖ F v).symm.trans (congrArg _ (mem_Treal.1 hv)))

theorem homW_injective : Function.Injective (homW t ϖ : BK.Hom P Q → _) := by
  rintro ⟨F, hF, _⟩ ⟨G, hG, _⟩ h
  have h1 := Matrix.toLin'.injective h
  obtain rfl : F = G := funext fun τ => Matrix.ext fun i j => congrArg Subtype.val
    (congrFun (ϖ.iTot_injective t K (inclO_injective (congrFun₂ h1 i j))) τ)
  rfl

end Hom

section Lat

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

def resLoc {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (T : LocLat G Qp LL O) (f : H →* G) (hf : Continuous f) : LocLat H Qp LL O where
  V := T.V
  ρ := T.ρ.comp f
  cont x := (T.cont x).comp hf
  L := ⟨T.L.T, fun g => T.L.stable (f g), T.L.fg, T.L.free, T.L.span⟩

def latW {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) : TW (OW l O) T →ₗ[O] TW (OW l O) T' :=
  TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le)

structure Ident (P : PhiMod O K l e a ι) (T : LocLat G ℚ_[l] K O) where

  j : (ι → OW l O) ≃ₗ[OW l O] TW (OW l O) T
  j_φ : ∀ v, j (phiW t ϖ P v) = TWmap (frobOW l O) T (j v)

omit [Module.Finite ℤ_[l] O] in

theorem frob_fixed (T : LocLat G ℚ_[l] K O) :
    (∀ y : TW (OW l O) T, ∃ b, TWmap (frobOW l O) T b - b = y) ∧
    (∀ b : TW (OW l O) T, TWmap (frobOW l O) T b = b ↔ ∃ x : ↥T.L.T, b = (1 : OW l O) ⊗ₜ[O] x) ∧
    Function.Injective fun x : ↥T.L.T => (1 : OW l O) ⊗ₜ[O] x := by
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WittTensorFixed.baseChange_flat (O := O) (frobW l) hs hk
    (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  have := T.L.free
  exact GlobalTheory.WittTensorFixed.tensor_flat (frobOW l O) h1 h2 h3

namespace Ident

variable {t ϖ} {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)

def res (f : H →* G) (hf : Continuous f) : Ident t ϖ P (resLoc T f hf) := ⟨I.j, I.j_φ⟩

def ofRes {f : H →* G} {hf : Continuous f} (I : Ident t ϖ P (resLoc T f hf)) : Ident t ϖ P T := ⟨I.j, I.j_φ⟩

def ofT : ↥T.L.T →ₗ[O] (ι → OW l O) :=
  (I.j.symm.toLinearMap.restrictScalars O).comp (TensorProduct.mk O (OW l O) ↥T.L.T 1)

theorem j_ofT (x : ↥T.L.T) : I.j (I.ofT x) = (1 : OW l O) ⊗ₜ[O] x := I.j.apply_symm_apply _

theorem ofT_injective : Function.Injective I.ofT := I.j.symm.injective.comp (frob_fixed T).2.2

theorem range_ofT : LinearMap.range I.ofT = Treal t ϖ P := by
  ext v
  rw [mem_Treal, ← I.j.injective.eq_iff, I.j_φ, (frob_fixed T).2.1]
  exact exists_congr fun x => by rw [← I.j.injective.eq_iff, j_ofT, eq_comm]

include I in

theorem exists_phiW_sub (y : ι → OW l O) : ∃ v, phiW t ϖ P v - v = y := by
  obtain ⟨b, hb⟩ := (frob_fixed T).1 (I.j y)
  exact ⟨I.j.symm b, I.j.injective (by rw [map_sub, I.j_φ, I.j.apply_symm_apply, hb])⟩

def act (s : GQ l) (g : G) : (ι → OW l O) →ₗ[O] (ι → OW l O) :=
  (I.j.symm.toLinearMap.restrictScalars O).comp
    ((TWact (galOW O s) T g).comp (I.j.toLinearMap.restrictScalars O))

theorem j_act (s : GQ l) (g : G) (v : ι → OW l O) : I.j (I.act s g v) = TWact (galOW O s) T g (I.j v) :=
  I.j.apply_symm_apply _

theorem act_ofT (s : GQ l) (g : G) (x : ↥T.L.T) : I.act s g (I.ofT x) = I.ofT (T.actT g x) :=
  I.j.injective (by
    rw [j_act, j_ofT, j_ofT, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one])

theorem act_smul (s : GQ l) (g : G) (r : OW l O) (v : ι → OW l O) :
    I.act s g (r • v) = galOW O s r • I.act s g v := by
  apply I.j.injective
  rw [j_act, map_smul I.j, map_smul I.j, j_act]
  induction I.j v using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem act_phiW (s : GQ l) (g : G) (v : ι → OW l O) :
    I.act s g (phiW t ϖ P v) = phiW t ϖ P (I.act s g v) := by
  apply I.j.injective
  rw [j_act, I.j_φ, I.j_φ, j_act]
  induction I.j v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [TWact, TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      galOW_frobOW]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem act_mul (s s' : GQ l) (g g' : G) (v : ι → OW l O) :
    I.act (s * s') (g * g') v = I.act s g (I.act s' g' v) := by
  apply I.j.injective
  rw [j_act, j_act, j_act]
  induction I.j v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, galOW_mul]
    exact congrArg _ (Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g g') x))
  | add x y hx hy => simp only [map_add, hx, hy]

def IsLMat (s : GQ l) (g : G) (Γ : Matrix ι ι (OA l O)) : Prop :=
  ∀ c : ι → OA l O, I.act s g (inclL t ϖ P c) = inclL t ϖ P (Γ *ᵥ fun i => galOA O s (c i))

theorem exists_isLMat_iff (s : GQ l) (g : G) :
    (∃ Γ, I.IsLMat s g Γ) ↔ ∀ v ∈ LA t ϖ P, I.act s g v ∈ LA t ϖ P := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨Γ, h⟩ _ ⟨c, rfl⟩
    exact ⟨_, (h c).symm⟩
  · choose y hy using fun j => h _ ⟨Pi.single j 1, rfl⟩
    have key : ∀ (d : ι → OA l O) (w : ι → ι → OA l O),
        inclL t ϖ P (∑ j, d j • w j) = ∑ j, inclO l O (d j) • inclL t ϖ P (w j) := fun d w => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
      exact congrArg _ (funext fun i => map_mul _ _ _)
    refine ⟨Matrix.of fun i j => y j i, fun c => ?_⟩
    have h1 : (Matrix.of fun i j => y j i) *ᵥ (fun i => galOA O s (c i)) = ∑ j, galOA O s (c j) • y j := by
      ext1 i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    conv_lhs => rw [pi_eq_sum_univ' c, key, map_sum]
    rw [h1, key]
    exact Finset.sum_congr rfl fun j _ => by rw [act_smul, galOW_inclO, hy]

end Ident

def IsMapOf {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (f : LatHom T.L T'.L)
    (F : BK.Hom P Q) : Prop :=
  ∀ v, I'.j (homW t ϖ F v) = latW f (I.j v)

theorem IsMapOf.unique {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L}
    {F F' : BK.Hom P Q} (h : IsMapOf I I' f F) (h' : IsMapOf I I' f F') : F = F' :=
  homW_injective t ϖ (LinearMap.ext fun v => I'.j.injective ((h v).trans (h' v).symm))

theorem IsMapOf.homW_ofT {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L}
    {F : BK.Hom P Q} (h : IsMapOf I I' f F) (x : ↥T.L.T) :
    homW t ϖ F (I.ofT x) = I'.ofT ⟨f.f x, f.T_le _ x.2⟩ :=
  I'.j.injective (by rw [h, I.j_ofT, I'.j_ofT]; rfl)

abbrev zlLat (T : LocLat G ℚ_[l] K O) : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)

def actZ (T : LocLat G ℚ_[l] K O) (g : G) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := T.actT g
    map_add' := map_add _
    map_smul' := fun c x => (T.actT g).map_smul (algebraMap ℤ_[l] O c) x }

def kappa (T : LocLat G ℚ_[l] K O) :
    letI := zlLat T
    WCb l ⊗[ℤ_[l]] ↥T.L.T →+ TW (OW l O) T :=
  letI := zlLat T
  TensorProduct.liftAddHom
    { toFun := fun w => (TensorProduct.mk O (OW l O) ↥T.L.T ((1 : O) ⊗ₜ w)).toAddMonoidHom
      map_zero' := by rw [tmul_zero, map_zero]; rfl
      map_add' := fun w w' => by rw [tmul_add, map_add]; rfl }
    fun z w x => by
      change ((1 : O) ⊗ₜ[ℤ_[l]] (z • w)) ⊗ₜ[O] x = ((1 : O) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[O] (algebraMap ℤ_[l] O z • x)
      rw [tmul_smul, ← algebraMap_smul O z, smul_tmul]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_tmul (T : LocLat G ℚ_[l] K O) (w : WCb l) (x : ↥T.L.T) :
    letI := zlLat T
    kappa T (w ⊗ₜ[ℤ_[l]] x) = ((1 : O) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[O] x := rfl

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_bijective (T : LocLat G ℚ_[l] K O) :
    letI := zlLat T
    Function.Bijective (kappa T) := by
  let _ := zlLat T
  have : IsScalarTower ℤ_[l] O ↥T.L.T := ⟨fun z x y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let E : TW (OW l O) T ≃+ WCb l ⊗[ℤ_[l]] ↥T.L.T :=
    (TensorProduct.comm O (OW l O) ↥T.L.T).toAddEquiv.trans
      ((AlgebraTensorModule.cancelBaseChange ℤ_[l] O O ↥T.L.T (WCb l)).toAddEquiv.trans
        (TensorProduct.comm ℤ_[l] ↥T.L.T (WCb l)).toAddEquiv)
  have h : ∀ y, E (kappa T y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w x => exact congrArg (fun y : ↥T.L.T => w ⊗ₜ[ℤ_[l]] y) (one_smul O x)
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨Function.LeftInverse.injective h, fun y => ⟨E y, E.injective (h _)⟩⟩

end Lat

variable (a O K) in

abbrev Lat : Type 1 := LocLat ↥(GK (ϖ.field a)) ℚ_[l] K O

variable {t ϖ} in

def IsBK {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) : Prop :=
  letI := zlLat T
  ∃ (E : FCrys l ↥(OL (ϖ.field a)))
    (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom]
      (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
    Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) j ∧
    ∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (j (E.tr (ϖ.toAinf a) x))) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)

structure BKMod (T : Lat a O K ϖ) where

  n : ℕ

  P : PhiMod O K l e a (Fin n)

  I : Ident t ϖ P T
  isBK : IsBK I

structure BKFunctor (C : Lat a O K ϖ → Prop) where

  obj : ∀ T, C T → BKMod t ϖ T

  map : ∀ {T T'} (hT : C T) (hT' : C T'), LatHom T.L T'.L → BK.Hom (obj T hT).P (obj T' hT').P
  isMapOf : ∀ {T T'} (hT : C T) (hT' : C T') (f : LatHom T.L T'.L),
    IsMapOf (obj T hT).I (obj T' hT').I f (map hT hT' f)

variable {t ϖ} in

def BKFunctor.ofExists {C : Lat a O K ϖ → Prop} (h₁ : ∀ T, C T → Nonempty (BKMod t ϖ T))
    (h₂ : ∀ {T T' : Lat a O K ϖ} (M : BKMod t ϖ T) (M' : BKMod t ϖ T') (f : LatHom T.L T'.L),
      ∃ F, IsMapOf M.I M'.I f F) : BKFunctor t ϖ C where
  obj T hT := (h₁ T hT).some
  map _ _ f := (h₂ _ _ f).choose
  isMapOf _ _ f := (h₂ _ _ f).choose_spec

variable (K) in

abbrev CrysBKFunctor (Pl : LocPrime l) : Type 1 :=
  BKFunctor t ϖ fun T : Lat a O K ϖ => IsCrys (Pl.PD (ϖ.field a)) T.ρ

section Conn

structure Conn {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) where

  nabla : Module.End K (Vec K a ι)
  leibniz : ∀ (f : ZMod a → K⟦X⟧) (v : Vec K a ι),
    nabla (f • v) = (fun τ => PowerSeries.derivative K (f τ)) • v + f • nabla v
  mem_MM : ∀ m ∈ P.MM, nabla m ∈ P.MM

namespace Conn

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (D : Conn P)

def N : Module.End K (Vec K a ι) where
  toFun v := (X : K⟦X⟧) • D.nabla v
  map_add' v w := by rw [map_add, smul_add]
  map_smul' c v := by rw [map_smul, smul_comm]; rfl

def desc (i : ℕ) : Module.End K (Vec K a ι) := Polynomial.aeval D.N (descPochhammer K i)

omit hl [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K]

theorem N_apply (v : Vec K a ι) : D.N v = (X : K⟦X⟧) • D.nabla v := rfl

theorem desc_zero (v : Vec K a ι) : D.desc 0 v = v := by simp [desc]

theorem desc_succ (i : ℕ) (v : Vec K a ι) : D.desc (i + 1) v = D.desc i (D.N v - i • v) := by
  rw [desc, descPochhammer_succ_right, map_mul, Module.End.mul_apply, ← desc, map_sub, Polynomial.aeval_X,
    map_natCast, LinearMap.sub_apply, Module.End.natCast_apply]

theorem N_mem {m : Vec K a ι} (hm : m ∈ P.MM) : D.N m ∈ P.MM :=
  P.MM.smul_mem (uIn (S O K e)) (D.mem_MM m hm)

theorem desc_mem (i : ℕ) {m : Vec K a ι} (hm : m ∈ P.MM) : D.desc i m ∈ P.MM := by
  induction i generalizing m with
  | zero => rwa [desc_zero]
  | succ i ih => rw [desc_succ]; exact ih (sub_mem (D.N_mem hm) (nsmul_mem hm i))

end Conn

namespace Conn

end Conn

namespace Ident

variable {t ϖ} {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T)

abbrev gal (g : ↥(GK (ϖ.field a))) : (ι → OW l O) →ₗ[O] (ι → OW l O) := I.act (g : GQ l) g

def Stable : Prop :=
  ∀ g : ↥(GK (ϖ.field a)), (∀ v ∈ LA t ϖ P, I.gal g v ∈ LA t ϖ P) ∧ ∀ v ∈ MA P, I.gal g v ∈ MA P

def Taylor (D : Conn P) : Prop :=
  ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (m : P.MM) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ z : ι → OCr l O, (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) -
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ =
        (l : OCr l O) ^ r • z

end Ident

end Conn

section Triv

variable (O K l e a ι) in

def unitMod : PhiMod O K l e a ι := ⟨fun _ => 1⟩

theorem frobMat_unitMod : frobMat t ϖ (unitMod l a e O K ι) = 1 := by
  rw [frobMat, ← Matrix.map_one (ϖ.iW t K) (map_zero _) (map_one _)]
  congr 1
  ext1 i j
  ext1 τ
  change (1 : Matrix ι ι (invE l e (A O K))) i j = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

variable {G : Type} [Group G] [TopologicalSpace G]

def unitIdent (T : LocLat G ℚ_[l] K O) (b : Module.Basis ι O ↥T.L.T) :
    Ident t ϖ (unitMod l a e O K ι) T where
  j := (b.baseChange (OW l O)).equivFun.symm
  j_φ v := by
    simp only [phiW_apply, frobMat_unitMod, Matrix.one_mulVec, Module.Basis.equivFun_symm_apply,
      Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one, map_sum, TWmap, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply]

theorem unitIdent_j (T : LocLat G ℚ_[l] K O) (b : Module.Basis ι O ↥T.L.T) (v : ι → OW l O) :
    (unitIdent t ϖ T b).j v = ∑ i, v i ⊗ₜ[O] b i := by
  simp only [unitIdent, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply, smul_tmul',
    smul_eq_mul, mul_one]

variable {ϖ} in

def IsTriv (T : Lat a O K ϖ) : Prop := ∀ g x, T.ρ g x = x

theorem kappa_sum (T : LocLat G ℚ_[l] K O) (b : Module.Basis ι O ↥T.L.T) {J : Type} [Fintype J] (o : J → O)
    (x : J × ι → (Wq l a)⟦X⟧) (m : Vec K a ι) (hm : m ∈ (unitMod l a e O K ι).M)
    (h : ∀ i, (fun τ => (⟨m τ i, mem_tot.1 hm τ i⟩ : A O K)) = ∑ k, o k • toAc t K (x (k, i))) :
    letI := zlLat T
    kappa T (∑ p : J × ι, inclW l (ϖ.ev a (x p)) ⊗ₜ[ℤ_[l]] (o p.1 • b p.2)) =
      (unitIdent t ϖ T b).j (toW t ϖ _ ⟨m, mem_ME_of_mem_M hm⟩) := by
  rw [unitIdent_j, map_sum, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : toW t ϖ _ ⟨m, mem_ME_of_mem_M hm⟩ i =
      inclO l O (ϖ.iTot t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩) :=
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  rw [h1, h, map_sum, map_sum, sum_tmul]
  refine Finset.sum_congr rfl fun k _ => (kappa_tmul T _ _).trans ?_
  rw [map_smul, map_smul, PiSys.iTot_toAc, inclO_tmul, smul_tmul]

theorem isBK_unitIdent {T : Lat a O K ϖ} (hT : IsTriv T) (b : Module.Basis ι O ↥T.L.T) :
    IsBK (unitIdent t ϖ T b) := by
  let _ := zlLat T
  have : IsScalarTower ℤ_[l] O ↥T.L.T := ⟨fun z x y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let o := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ x : Module.Free.ChooseBasisIndex ℤ_[l] O × ι → (Wq l a)⟦X⟧,
      unitPowMap (ϖ.field a) (o.smulTower b) (fun p => ϖ.ev a (x p)) =
        ∑ p, inclW l (ϖ.ev a (x p)) ⊗ₜ[ℤ_[l]] (o p.1 • b p.2) := fun x => by
    simp only [unitPowMap_apply, Module.Basis.smulTower_apply]
  have key2 : ∀ y : TW (OW l O) T, (∃ x : Module.Free.ChooseBasisIndex ℤ_[l] O × ι → (Wq l a)⟦X⟧,
      y = kappa T (unitPowMap (ϖ.field a) (o.smulTower b) (fun p => ϖ.ev a (x p)))) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ (unitMod l a e O K ι).M),
        y = (unitIdent t ϖ T b).j (toW t ϖ _ ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [key]
    constructor
    · rintro ⟨x, rfl⟩
      have hm : (fun τ i => (((∑ k, o k • toAc t K (x (k, i))) τ : A O K) : K⟦X⟧)) ∈
          (unitMod l a e O K ι).M := mem_tot.2 fun τ i => Subtype.prop _
      exact ⟨_, hm, kappa_sum t ϖ T b o x _ hm fun _ => rfl⟩
    · rintro ⟨m, hm, rfl⟩
      choose x hx using fun i => exists_eq_sum_toAc t K o fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
      exact ⟨fun p => x p.2 p.1, (kappa_sum t ϖ T b o (fun p => x p.2 p.1) m hm hx).symm⟩
  exact ⟨_, unitPowMap _ (o.smulTower b), realises_unitPow _ _ _ fun g x => Subtype.ext (hT g x), key2⟩

def latBasis (T : LocLat G ℚ_[l] K O) : Module.Basis (Fin (Module.finrank O ↥T.L.T)) O ↥T.L.T :=
  haveI : Nontrivial O := (algebraMap O K).domain_nontrivial
  haveI := T.L.free
  haveI := Module.Finite.iff_fg.2 T.L.fg
  Module.finBasis O ↥T.L.T

omit [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem galOCr_idem (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOCr O g (idem (constC t) τ) = idem (constC t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  rw [idem, constC, AlgHom.comp_apply, galOCr_toOCr, galOA_constA t h]

variable (G) in

def unitLat : LocLat G ℚ_[l] K O where
  V := K
  ρ := 1
  fdim := inferInstance
  cont _ := continuous_const
  L :=
    { T := LinearMap.range (Algebra.linearMap O K)
      stable := fun _ _ hx => hx
      fg := by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O K) IsUnitBall.inj)
      span := eq_top_iff.2 fun x _ => by
        have h : (1 : K) ∈ Submodule.span K (LinearMap.range (Algebra.linearMap O K) : Set K) :=
          Submodule.subset_span ⟨1, by simp⟩
        simpa using Submodule.smul_mem _ x h }

end Triv

section FinExt

variable (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]

variable (a) in

abbrev CrysBKFunctorOL [HasUnr a LL] (Pl : LocPrime l) : Type 1 :=
  CrysBKFunctor ↥LL.1 (thetaW a LL) ϖ Pl

end FinExt

end GlobalTheory.BKReal
