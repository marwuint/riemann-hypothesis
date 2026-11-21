import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsOrthSplit
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mi MeasureTheory NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_cols (S : HSp D) {a b : ℕ} (M : Matrix (Fin S.rank) (Fin a) D.host.E) (N : Matrix (Fin S.rank) (Fin b) D.host.E)
    (i : Fin a) (l : Fin b) : (Mᴴ * S.gram * N) i l =
      S.hT (S.frame.equivFun.symm fun k => M k i) (S.frame.equivFun.symm fun k => N k l) := by
  simp only [Module.Basis.equivFun_symm_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum, HSpace.gram]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem col_frameMat (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (i : Fin B.rank) :
    (A.frame.equivFun.symm fun k => frameMat A B ι k i) = ι (B.frame i) := by
  simp only [frameMat, LinearMap.toMatrix_apply, Module.Basis.equivFun_symm_apply, Module.Basis.sum_repr]

theorem frameMat_comp (A B C : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (κ : C.V →ₗ[D.host.E] B.V) :
    frameMat A C (ι ∘ₗ κ) = frameMat A B ι * frameMat B C κ := LinearMap.toMatrix_comp _ _ _ _ _

theorem gram_frameMat {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : HSpace.IsIsomEmb B A ι) :
    (frameMat A B ι)ᴴ * A.gram * frameMat A B ι = B.gram := by
  ext i l
  rw [gram_cols, col_frameMat, col_frameMat, h]; rfl

theorem hT_symm_zero (S : HSp D) {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem exists_piT (D : D7) : ∃ π : D.host.E, star π * π = (D.sp.T : D.host.E) := by
  obtain ⟨π, -, h, -⟩ := D.T_norm D.u₀
  refine ⟨π, ?_⟩
  rw [D.sp_T, ← h, mul_comm, GlobalTheory.StdFrames.conj_eq_star]

def piT (D : D7) : D.host.E := (exists_piT D).choose

theorem star_piT_mul (D : D7) : star (piT D) * piT D = (D.sp.T : D.host.E) := (exists_piT D).choose_spec

theorem T_ne_zero (D : D7) : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero

theorem piT_ne_zero (D : D7) : piT D ≠ 0 := fun h => T_ne_zero D (by rw [← star_piT_mul, h, mul_zero])

@[reducible] def lineT (D : D7) (neg : Bool) : HSp D where
  V := Fin 1 → D.host.E
  hT := Examples₂.diagForm 1 fun _ => neg
  herm := Examples₂.diagForm_isSymm 1 _
  nondeg := Examples₂.diagForm_nondeg 1 _
  rank := 1
  rank_eq := Module.finrank_fin_fun _
  frame := (Pi.basisFun D.host.E (Fin 1)).unitsSMul fun _ => Units.mk0 (piT D) (piT_ne_zero D)
  sig := fun _ => if neg then (0, 1) else (1, 0)
  L0 := Examples₂.stdLat 1
  standardTuple_isLattice := Examples₂.stdLat_isLattice 1
  baseLattice_isUnimodular := Examples₂.stdLat_unimod Examples₂.star_isIntegral 1 _

abbrev lineNeg (D : D7) : HSp D := lineT D true

abbrev linePos (D : D7) : HSp D := lineT D false

theorem lineT_gram (neg : Bool) (i l : Fin 1) :
    (lineT D neg).gram i l = if neg then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E) := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : l = 0 := Subsingleton.elim _ _
  change Examples₂.diagForm 1 (fun _ => neg) _ _ = _
  rw [Examples₂.diagForm_apply, ← star_piT_mul]
  cases neg <;> simp [Module.Basis.unitsSMul_apply, Examples₂.sgn, Units.smul_def]

theorem linePos_gram (i l : Fin 1) : (linePos D).gram i l = (D.sp.T : D.host.E) := lineT_gram false i l

theorem hasSignature_nat {T : ℕ} (hT : 0 < T) :
    Formalism.UG.HasSignature (Matrix.of fun _ _ : Fin 1 => (T : ℂ)) 1 0 ∧
      Formalism.UG.HasSignature (Matrix.of fun _ _ : Fin 1 => -(T : ℂ)) 0 1 := by
  have h1 : ((√(T : ℝ) : ℝ) : ℂ) * ((√(T : ℝ) : ℝ) : ℂ) = T := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T)]; simp
  have h2 : ((√(T : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => by
    rw [h, mul_zero] at h1
    exact hT.ne' (by exact_mod_cast h1.symm)
  constructor
  · refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp) (Matrix.of fun _ _ => ((√(T : ℝ) : ℝ) : ℂ)⁻¹) ?_
    ext (r | r) (s | s)
    · obtain rfl : r = s := Subsingleton.elim _ _
      simp [Matrix.mul_apply, Formalism.UG.Jpq]
      rw [← h1]; field_simp
    · exact s.elim0
    · exact r.elim0
    · exact r.elim0
  · refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp) (Matrix.of fun _ _ => ((√(T : ℝ) : ℝ) : ℂ)⁻¹) ?_
    ext (r | r) (s | s)
    · exact r.elim0
    · exact r.elim0
    · exact s.elim0
    · obtain rfl : r = s := Subsingleton.elim _ _
      simp [Matrix.mul_apply, Formalism.UG.Jpq]
      rw [← h1]; field_simp

theorem isLineVec_lineT (neg : Bool) : IsLineVec (lineT D neg) fun _ => 1 := by
  refine ⟨rfl, ?_⟩
  have := T_ne_zero D
  cases neg <;> simp [dotProduct, Matrix.mulVec, lineT_gram, this]

def lineMap (neg : Bool) (S : HSp D) (v : S.V) : (lineT D neg).V →ₗ[D.host.E] S.V :=
  (lineT D neg).frame.constr D.host.E fun _ => v

theorem lineMap_frame (neg : Bool) (S : HSp D) (v : S.V) (i : Fin 1) : lineMap neg S v ((lineT D neg).frame i) = v :=
  Module.Basis.constr_basis _ _ _ _

theorem lineMap_apply (neg : Bool) (S : HSp D) (v : S.V) (a : (lineT D neg).V) :
    lineMap neg S v a = (lineT D neg).frame.repr a 0 • v := by
  rw [lineMap, Module.Basis.constr_apply_fintype]
  exact Fin.sum_univ_one _

theorem lineMap_isom {neg : Bool} {S : HSp D} {v : S.V}
    (hv : S.hT v v = if neg then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E)) :
    HSpace.IsIsomEmb (lineT D neg) S (lineMap neg S v) := fun a b => by
  have e : ∀ a : (lineT D neg).V, a = (lineT D neg).frame.repr a 0 • (lineT D neg).frame 0 := fun a => by
    conv_lhs => rw [← (lineT D neg).frame.sum_repr a]
    exact Fin.sum_univ_one _
  rw [lineMap_apply, lineMap_apply]
  conv_rhs => rw [e a, e b]
  simp only [LinearMap.map_smulₛₗ₂, map_smul, hv]
  rw [← lineT_gram neg 0 0]; rfl

theorem exists_topScalar (D : D7) : ∃ l : D.host.E,
    star l * l * (D.sp.X D.R.m).hT D.sp.z D.sp.z = (D.sp.T : D.host.E) := by
  have hr : (D.sp.X D.R.m).rank = D.sp.X'.rank + 1 := by
    have h1 := D.sp.X_rank D.R.m le_rfl
    have h2 := D.sp.X'_rank
    have h3 := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N, Ranks.rankX', Ranks.r] at h1 h2
    omega
  obtain ⟨b, hb, hd, hs, a, ha, hdet⟩ := GlobalTheory.FrameComplement.exists_complement (p := 1) (q := 0) D.sp.cm.cmUnram.2.1
    D.sp.X' (D.sp.X D.R.m) D.sp.iX' D.sp.iX'_isom hr
    (fun τ => by have := D.sp.X'_sig τ; rwa [D.X'_posDef τ] at this)
    (fun τ => by have := D.sp.X_sig D.R.m τ; rw [D.X_posDef D.R.m le_rfl τ] at this; rw [← hr]; exact this)
  have hX := GlobalTheory.FrameComplement.gram_det_ne D.sp.X'
  have hT0 := T_ne_zero D
  obtain ⟨P, -, hP⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm D.host.F D.host.E D.sp.cm 1
    (Matrix.of fun i l => (D.sp.X D.R.m).hT (b i) (b l)) (Matrix.of fun _ _ => (D.sp.T : D.host.E))
    (Matrix.ext fun i l => (D.sp.X D.R.m).herm.eq _ _) (by ext i l; simp) hd (by simpa using hT0)
    (fun τ => ⟨_, _, hs τ, by
      convert (hasSignature_nat D.sp.T_prime.pos).1 using 1
      ext i l; simp⟩)
    (by
      have h2 := (((GlobalTheory.DetNorm.isN_det (D.sp.X D.R.m)).mul ((GlobalTheory.DetNorm.isN_det D.sp.X').inv
        (GlobalTheory.DetNorm.star_det _))).mul (GlobalTheory.DetNorm.isN_star a⁻¹)).mul ((GlobalTheory.DetNorm.isNormFromTensorFiniteAdele_levelNormT (D := D)).inv (by simp))
      have ha' : star a ≠ 0 := star_ne_zero.2 ha
      have h3 : ∀ x g u : D.host.E, x ≠ 0 → star a * a * x * g * x⁻¹ * (star a⁻¹ * a⁻¹) * u⁻¹ = g / u :=
        fun x g u hx => by rw [star_inv₀, div_eq_mul_inv]; field_simp
      rw [hdet, h3 _ _ _ hX] at h2
      rw [Matrix.det_unique (Matrix.of fun _ _ : Fin 1 => (D.sp.T : D.host.E))]
      exact h2)

  let o : OrthDec (D.sp.X D.R.m) D.sp.X' (linePos D) :=
    { iA := frameMat _ _ D.sp.iX'
      iB := frameMat _ _ (lineMap false _ (P 0 0 • b 0))
      isoA := gram_frameMat D.sp.iX'_isom
      isoB := gram_frameMat (lineMap_isom (by
        have := congrFun (congrFun hP 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.of_apply] at this
        simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply, Bool.false_eq_true, if_false]
        linear_combination this))
      orth := by
        ext i l
        rw [gram_cols, col_frameMat, col_frameMat, lineMap_frame]
        have h0 : (D.sp.X D.R.m).hT (D.sp.iX' (D.sp.X'.frame l)) (P 0 0 • b 0) = 0 := by
          rw [map_smul, hb, smul_zero]
        rw [hT_symm_zero _ h0]; rfl
      rank_add := hr.symm }
  let y : Fin (D.sp.X D.R.m).rank → D.host.E := (D.sp.X D.R.m).frame.equivFun D.sp.z
  let Y : Matrix (Fin (D.sp.X D.R.m).rank) (Fin 1) D.host.E := Matrix.of fun k _ => y k
  have hY : ∀ i, ((D.sp.X D.R.m).frame.equivFun.symm fun k => Y k i) = D.sp.z := fun i =>
    (D.sp.X D.R.m).frame.equivFun.symm_apply_apply _
  have h1 : o.iAᴴ * (D.sp.X D.R.m).gram * Y = 0 := by
    ext i l
    rw [gram_cols, hY, col_frameMat, D.sp.z_orth]; rfl
  have h2 : Y = o.iB * (o.qB * Y) := by
    conv_lhs => rw [← Matrix.one_mul Y, ← o.iA_qA_add]
    rw [Matrix.add_mul, Matrix.mul_assoc, OrthDec.qA, Matrix.mul_assoc _ _ Y, h1, Matrix.mul_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc]
  have h3 : Yᴴ * (D.sp.X D.R.m).gram * Y = (o.qB * Y)ᴴ * (linePos D).gram * (o.qB * Y) := by
    conv_lhs => rw [h2]
    rw [← o.isoB, Matrix.conjTranspose_mul o.iB]
    simp only [Matrix.mul_assoc]
  have h4 := congrFun (congrFun h3 0) 0
  rw [gram_cols, hY] at h4
  simp only [Matrix.mul_apply (M := (o.qB * Y)ᴴ * (linePos D).gram), Matrix.mul_apply (M := (o.qB * Y)ᴴ),
    Fin.sum_univ_one, Matrix.conjTranspose_apply, linePos_gram] at h4
  generalize (o.qB * Y) 0 0 = c at h4
  have hc : c ≠ 0 := fun h => D.sp.z_anis (by rw [h4, h, mul_zero])
  have hc' : star c ≠ 0 := star_ne_zero.2 hc
  refine ⟨c⁻¹, ?_⟩
  rw [h4, star_inv₀]; field_simp

section Zero

variable {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem matrix_mul_empty_inner {a b : ℕ} (M : Mx D a 0) (N : Mx D 0 b) : M ⬝ N = 0 := by
  ext i l; simp [Matrix.mul_apply]

theorem witt_decomposition_zero_section_embed_eq_one : d.j0 ⬝ d.p0 = 1 := by
  have h := d.sum_eq_one
  rwa [matrix_mul_empty_inner, matrix_mul_empty_inner d.jY, zero_add, add_zero] at h

def emb0Equiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun g := ofMat S₀ (d.p0 ⬝ (mt S g ⬝ d.j0)) (by
    have h := d.gA_eq
    rw [matrix_mul_empty_inner (adj d.pY), matrix_mul_empty_inner (adj d.pX), zero_add, add_zero] at h
    rw [adj_mul, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, cancel₃ h.symm, cancel₃ (mt_unitary S g), d.gram_00])
  left_inv g := mt_injective S₀ (by rw [mt_ofMat, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [← Matrix.mul_one (mt S (d.emb0 _)), ← witt_decomposition_zero_section_embed_eq_one d, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, cancel₂ (witt_decomposition_zero_section_embed_eq_one d),
      Matrix.one_mul, Matrix.mul_assoc, witt_decomposition_zero_section_embed_eq_one, Matrix.mul_one])
  map_mul' := map_mul d.emb0

end Zero

def IsUPair (r : ℕ) (μ : Measure (SUp D r)) (𝓕 : Set (SUp D r)) : Prop :=
  μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratSU D r) 𝓕 μ ∧ μ 𝓕 = 1

def rho (D : D7) (j : ℕ) : ℕ := (D.R.m - 1 - j) / 2

theorem rank_Y (j : ℕ) (hj : j < D.R.m) :
    (D.sp.Y j).rank = (D.sp.X j).rank + 2 * rho D j + (if Even j then 1 else 0) := by
  have h1 := D.sp.X_rank j hj.le
  have h2 := D.sp.Y_rank j hj.le
  obtain ⟨a, ha⟩ := D.R.m_even
  have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r] at h1 h2
  unfold rho
  split_ifs with he
  · obtain ⟨b, hb⟩ := he; omega
  · rw [Nat.not_even_iff_odd] at he; obtain ⟨b, hb⟩ := he; omega

theorem odd_c {j : ℕ} (hj : j < D.R.m) (he : Even j) : (D.R.m - 1 - j) % 2 = 1 :=
  (GlobalTheory.NormalFramesLevels.even_iff_odd_c hj).1 he

structure Frames (D : D7) where
  e : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E
  lam : D.host.E
  aux : IsAdaptedVectorSystem e ev z
  lam_norm : star lam * lam * (D.sp.X D.R.m).hT D.sp.z D.sp.z = (D.sp.T : D.host.E)

namespace Frames

variable (F : Frames D)

def colMat (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := fun k i => F.e j i k

def dualMat (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := fun k i => F.ev j i k

def base (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E :=
  fun k i => if i.1 < rho D j then F.e j i k else F.z j k

abbrev V0 (D : D7) (j : ℕ) : HSp D := hsum (D.sp.X j) (lineNeg D)

def embeddingLineSum (j : ℕ) : (V0 D j).V →ₗ[D.host.E] (D.sp.Y j).V :=
  LinearMap.coprod (D.sp.iXY j) (lineMap true (D.sp.Y j) (vecY j (F.z j)))

theorem embedding_line_sum_inl (j : ℕ) : F.embeddingLineSum j ∘ₗ LinearMap.inl D.host.E _ _ = D.sp.iXY j := by
  ext x; simp [embeddingLineSum]

def orthogonalDecompLineSum (D : D7) (j : ℕ) : OrthDec (V0 D j) (D.sp.X j) (lineNeg D) where
  iA := frameMat _ _ (LinearMap.inl D.host.E _ _)
  iB := frameMat _ _ (LinearMap.inr D.host.E _ _)
  isoA := gram_frameMat (isIsomEmb_inl _ _)
  isoB := gram_frameMat (isIsomEmb_inr _ _)
  orth := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat, col_frameMat]
    change (D.sp.X j).hT 0 _ + (lineNeg D).hT _ 0 = 0
    rw [map_zero, map_zero, LinearMap.zero_apply, add_zero]
  rank_add := rfl

section Rel

variable {j : ℕ} (hj : j < D.R.m)
include hj

theorem hT_X_e {i : ℕ} (hi : i < rho D j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.e j i)) = 0 := by
  have h := (F.aux j hj).2.2 x i (by unfold rho at hi; omega)
  unfold adaptedVector at h
  rwa [if_pos (show i < (D.R.m - 1 - j) / 2 from hi)] at h

theorem hT_X_ev {i : ℕ} (hi : i < rho D j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.ev j i)) = 0 := by
  unfold rho at hi
  have h := (F.aux j hj).2.2 x (D.R.m - 1 - j - 1 - i) (by omega)
  unfold adaptedVector at h
  rwa [if_neg (by omega), if_neg (by omega), show D.R.m - 1 - j - 1 - (D.R.m - 1 - j - 1 - i) = i by omega] at h

theorem hT_X_alt (he : Even j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.z j)) = 0 := by
  have hc := odd_c hj he
  have h := (F.aux j hj).2.2 x ((D.R.m - 1 - j) / 2) (by omega)
  unfold adaptedVector at h
  rwa [if_neg (lt_irrefl _), if_pos ⟨hc, rfl⟩] at h

theorem z_norm (he : Even j) : (D.sp.Y j).hT (vecY j (F.z j)) (vecY j (F.z j)) = -(D.sp.T : D.host.E) :=
  ((F.aux j hj).2.1 (odd_c hj he)).1

theorem embedding_line_sum_orthogonal (he : Even j) {v : (D.sp.Y j).V} (h1 : ∀ x, (D.sp.Y j).hT (D.sp.iXY j x) v = 0)
    (h2 : (D.sp.Y j).hT (vecY j (F.z j)) v = 0) (w : (V0 D j).V) : (D.sp.Y j).hT (F.embeddingLineSum j w) v = 0 := by
  change (D.sp.Y j).hT (D.sp.iXY j w.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) w.2) v = 0
  rw [map_add, LinearMap.add_apply, h1, lineMap_apply, LinearMap.map_smulₛₗ₂, h2, smul_zero, add_zero]

theorem embedding_line_sum_isometry (he : Even j) : HSpace.IsIsomEmb (V0 D j) (D.sp.Y j) (F.embeddingLineSum j) := fun a b => by
  have h1 : ∀ x c, (D.sp.Y j).hT (D.sp.iXY j x) (lineMap true (D.sp.Y j) (vecY j (F.z j)) c) = 0 := fun x c => by
    rw [lineMap_apply, map_smul, F.hT_X_alt hj he, smul_zero]
  have h2 := lineMap_isom (neg := true) (F.z_norm hj he)
  change (D.sp.Y j).hT (D.sp.iXY j a.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) a.2)
    (D.sp.iXY j b.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) b.2) = (D.sp.X j).hT a.1 b.1 + (lineNeg D).hT a.2 b.2
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, hT_symm_zero _ (h1 _ _), D.sp.iXY_isom j hj, h2,
    add_zero, zero_add]

variable {r : ℕ} (hr : r = rho D j)
include hr

theorem col_col : (F.colMat j r)ᴴ * (D.sp.Y j).gram * F.colMat j r = 0 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ((F.aux j hj).1 i i.2 l l.2).2.1

theorem dual_dual : (F.dualMat j r)ᴴ * (D.sp.Y j).gram * F.dualMat j r = 0 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ((F.aux j hj).1 i i.2 l l.2).2.2

theorem dual_col : (F.dualMat j r)ᴴ * (D.sp.Y j).gram * F.colMat j r = 1 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ?_
  refine ((D.sp.Y j).herm.eq _ _).symm.trans ?_
  refine (congrArg (starRingEnd D.host.E) ((F.aux j hj).1 l l.2 i i.2).1).trans ?_
  rw [Matrix.one_apply]
  by_cases h : i = l
  · subst h; simp
  · rw [if_neg h, if_neg fun e => h (Fin.ext e.symm), map_zero]

end Rel

def hypEven {j : ℕ} (hj : j < D.R.m) (he : Even j) {r : ℕ} (hr : r = rho D j) : HypDec (D.sp.Y j) (V0 D j) r where
  e := F.colMat j r
  e' := F.dualMat j r
  i₀ := frameMat _ _ (F.embeddingLineSum j)
  ee := F.col_col hj hr
  e'e' := F.dual_dual hj hr
  e'e := F.dual_col hj hr
  iso := gram_frameMat (F.embedding_line_sum_isometry hj he)
  i₀e := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.embedding_line_sum_orthogonal hj he (F.hT_X_e hj (hr ▸ l.2)) (((F.aux j hj).2.1 (odd_c hj he)).2 l (hr ▸ l.2 : l.1 < rho D j)).1 _
  i₀e' := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.embedding_line_sum_orthogonal hj he (F.hT_X_ev hj (hr ▸ l.2)) (((F.aux j hj).2.1 (odd_c hj he)).2 l (hr ▸ l.2 : l.1 < rho D j)).2 _
  rank_add := by
    have h := rank_Y j hj
    rw [if_pos he] at h
    change (D.sp.X j).rank + 1 + 2 * r = _
    omega

def hypOdd {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j) {r : ℕ} (hr : r = rho D j) : HypDec (D.sp.Y j) (D.sp.X j) r where
  e := F.colMat j r
  e' := F.dualMat j r
  i₀ := frameMat _ _ (D.sp.iXY j)
  ee := F.col_col hj hr
  e'e' := F.dual_dual hj hr
  e'e := F.dual_col hj hr
  iso := gram_frameMat (D.sp.iXY_isom j hj)
  i₀e := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.hT_X_e hj (hr ▸ l.2) _
  i₀e' := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.hT_X_ev hj (hr ▸ l.2) _
  rank_add := by
    have h := rank_Y j hj
    rw [if_neg ho] at h
    omega

def hypTop (D : D7) : HypDec (D.sp.Y D.R.m) D.sp.X' 0 where
  e := 0
  e' := 0
  i₀ := frameMat _ _ D.sp.eYm.toLinearMap
  ee := Matrix.ext fun i => i.elim0
  e'e' := Matrix.ext fun i => i.elim0
  e'e := Matrix.ext fun i => i.elim0
  iso := gram_frameMat D.sp.eYm_isom
  i₀e := Matrix.ext fun _ l => l.elim0
  i₀e' := Matrix.ext fun _ l => l.elim0
  rank_add := by rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl

theorem frameMat_iXY (j : ℕ) : frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) =
    frameMat (D.sp.Y j) (V0 D j) (F.embeddingLineSum j) * (orthogonalDecompLineSum D j).iA := by
  rw [← F.embedding_line_sum_inl j]; exact frameMat_comp _ _ _ _ _

def besDat {j : ℕ} (hj : j < D.R.m) (he : Even j) : BesDat (D.sp.X j) (D.sp.Y j) (D.sp.iXY j) :=
  toBesDat (F.hypEven hj he rfl) (orthogonalDecompLineSum D j) (isLineVec_lineT true) one_ne_zero (D.sp.iXY j) (F.frameMat_iXY j)

theorem besDat_rho {j : ℕ} (hj : j < D.R.m) (he : Even j) : (F.besDat hj he).ρ = rho D j := rfl

theorem besDat_e {j : ℕ} (hj : j < D.R.m) (he : Even j) : (F.besDat hj he).e = F.colMat j (rho D j) := rfl

theorem besDat_c {j : ℕ} (hj : j < D.R.m) (he : Even j) (i) : (F.besDat hj he).c i = 1 := rfl

theorem besDat_y {j : ℕ} (hj : j < D.R.m) (he : Even j) : ((F.besDat hj he).y : GA D (D.sp.Y j)) = 1 := rfl

def emb (j : ℕ) : GA D (D.sp.X j) →* GA D (D.sp.Y j) :=
  if hj : j < D.R.m then
    (if he : Even j then embA (F.hypEven hj he rfl) (orthogonalDecompLineSum D j) else (F.hypOdd hj he rfl).emb0)
  else 1

def embYm (D : D7) : GA D D.sp.X' →* GA D (D.sp.Y D.R.m) := (hypTop D).emb0

abbrev grpN (j : ℕ) : Subgroup (GA D (D.sp.Y j)) := NFlag (D.sp.Y j) (F.colMat j (rho D j))

def psiN (ψ : AddChar (AF D.host.F) ℂ) (j : ℕ) : GA D (D.sp.Y j) → ℂ :=
  if h : j < D.R.m ∧ Even j then besChar ψ (F.besDat h.1 h.2) else psiU ψ (D.sp.Y j) (F.colMat j (rho D j))

def std (D : D7) : Frames D where
  e := GlobalTheory.NormalFramesLevels.eC D
  ev := GlobalTheory.NormalFramesLevels.evC D
  z := GlobalTheory.NormalFramesLevels.zC D
  lam := (exists_topScalar D).choose
  aux := GlobalTheory.NormalFramesLevels.normal_frame_level_conditions_C
  lam_norm := (exists_topScalar D).choose_spec

instance : Inhabited (Frames D) := ⟨std D⟩

end Frames

structure Meas (F : Frames D) where
  μY : ∀ j, Measure (GA D (D.sp.Y j))
  fdY : ∀ j, Set (GA D (D.sp.Y j))
  μX : ∀ j, Measure (GA D (D.sp.X j))
  fdX : ∀ j, Set (GA D (D.sp.X j))
  μX' : Measure (GA D D.sp.X')
  fdX' : Set (GA D D.sp.X')
  μN : ∀ j, Measure (F.grpN j)
  fdN : ∀ j, Set (F.grpN j)
  μU : ∀ r, Measure (SUp D r)
  fdU : ∀ r, Set (SUp D r)
  μM : ∀ a b, Measure (Mx D a b)
  fdM : ∀ a b, Set (Mx D a b)
  quotY : ∀ j, IsQuotPair (D.sp.Y j) (μY j) (fdY j)
  quotX : ∀ j, IsQuotPair (D.sp.X j) (μX j) (fdX j)
  quotX' : IsQuotPair D.sp.X' μX' fdX'
  unitN : ∀ j, GlobalTheory.Per.IsUnitN (D.sp.Y j) (F.colMat j (rho D j)) (μN j) (fdN j)
  unitU : ∀ r, IsUPair r (μU r) (fdU r)
  unitM : ∀ a b, IsCovolOne (Formalism.IndefR.Eqv.ratMx D a b) (μM a b) (fdM a b)
  tieLast : ∀ j, j + 1 = D.R.m → μY j = (μX j).map (F.emb j)
  tieTop : μY D.R.m = μX'.map (Frames.embYm D)

namespace Meas

end Meas

end GlobalTheory.CompanionTheory.Chain

end
