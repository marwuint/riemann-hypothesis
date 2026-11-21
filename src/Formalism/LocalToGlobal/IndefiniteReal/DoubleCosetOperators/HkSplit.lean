import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.HeckeCommuteOfCompatibility
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

open scoped TensorProduct

namespace Formalism.IndefR.NX

section Ext

variable {S S' R : Type} [CommRing S] [CommRing S'] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def extM (ι : S →ₙ+* R) (A : Matrix n n S) : Matrix n n R := (1 - ι 1) • (1 : Matrix n n R) + A.map ι

theorem idem_mul (ι : S →ₙ+* R) (x : S) : ι 1 * ι x = ι x := by rw [← map_mul, one_mul]

theorem compl_mul (ι : S →ₙ+* R) (x : S) : (1 - ι 1) * ι x = 0 := by
  rw [sub_mul, one_mul, idem_mul, sub_self]

theorem map_mul_nu (ι : S →ₙ+* R) (A B : Matrix n n S) : (A * B).map ι = A.map ι * B.map ι := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem compl_smul_map (ι : S →ₙ+* R) (A : Matrix n n S) : (1 - ι 1) • A.map ι = 0 := by
  ext i j; simp [compl_mul]

theorem extM_one (ι : S →ₙ+* R) : extM ι (1 : Matrix n n S) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [extM]
  · simp [extM, Matrix.one_apply, h]

theorem extM_mul (ι : S →ₙ+* R) (A B : Matrix n n S) : extM ι (A * B) = extM ι A * extM ι B := by
  have hc : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
    have h := idem_mul ι 1
    linear_combination h
  simp only [extM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    compl_smul_map, smul_smul, hc, map_mul_nu, add_zero, zero_add]

def extHom (ι : S →ₙ+* R) : Matrix n n S →* Matrix n n R where
  toFun := extM ι
  map_one' := extM_one ι
  map_mul' := extM_mul ι

def extGL (ι : S →ₙ+* R) : GL n S →* GL n R := Units.map (extHom ι)

theorem extGL_coe (ι : S →ₙ+* R) (g : GL n S) : ((extGL ι g : GL n R) : Matrix n n R) = extM ι g := rfl

theorem extM_cT (ι : S →ₙ+* R) (σS : S →+* S) (σR : R →+* R) (hι : ∀ x, ι (σS x) = σR (ι x)) (A : Matrix n n S) :
    cT σR (extM ι A) = extM ι (cT σS A) := by
  have he : σR (ι 1) = ι 1 := by rw [← hι, map_one]
  ext i j
  by_cases h : i = j
  · subst h; simp [cT, extM, hι, he]
  · simp [cT, extM, Matrix.one_apply, h, Ne.symm h, hι]

theorem extGL_mem (ι : S →ₙ+* R) (σS : S →+* S) (σR : R →+* R) (hι : ∀ x, ι (σS x) = σR (ι x))
    (JS : Matrix n n S) (JR : Matrix n n R) (hJ : JS.map ι = ι 1 • JR) (g : GL n S) (hg : g ∈ UJ σS JS) :
    extGL ι g ∈ UJ σR JR := by
  have hg' : cT σS (g : Matrix n n S) * JS * (g : Matrix n n S) = JS := hg
  show cT σR (extM ι (g : Matrix n n S)) * JR * extM ι (g : Matrix n n S) = JR
  rw [extM_cT ι σS σR hι]
  set A := cT σS (g : Matrix n n S)
  set B := (g : Matrix n n S)
  have k1 : A.map ι * JR = (A * JS).map ι := by
    rw [map_mul_nu, hJ, Matrix.mul_smul]
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, idem_mul]
  have k2 : (1 - ι 1) • (JR * B.map ι) = 0 := by rw [← Matrix.mul_smul, compl_smul_map, Matrix.mul_zero]
  have k3 : (1 - ι 1) • (A.map ι * JR) = 0 := by rw [k1, compl_smul_map]
  have hc : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
    have h := idem_mul ι 1
    linear_combination h
  calc extM ι A * JR * extM ι B
      = (1 - ι 1) • JR + A.map ι * JR * B.map ι := by
        simp only [extM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          smul_smul, hc, k2, k3, add_zero, zero_add]
    _ = (1 - ι 1) • JR + ι 1 • JR := by rw [k1, ← map_mul_nu, hg', hJ]
    _ = JR := by rw [← add_smul, sub_add_cancel, one_smul]

end Ext

section Place

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def inrL : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)

theorem inrL_mul (a c : Af F) : inrL (a * c) = inrL a * inrL c := Prod.ext (mul_zero (0 : Ainf F)).symm rfl

def inrT : Af F ⊗[F] E →ₙ+* AF F ⊗[F] E where
  toFun := LinearMap.rTensor E inrL
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, inrL_mul]

def jv (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* AF F ⊗[F] E :=
  (inrT (E := E)).comp ((Algebra.TensorProduct.comm F E (Af F)).toRingEquiv.toRingHom.toNonUnitalRingHom.comp
    (Formalism.UG.P.afsplitIE (E := E) v))

theorem jv_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (b : v.adicCompletion F) :
    jv v (a ⊗ₜ[F] b) = inrL (Formalism.UG.P.afsplitI v b) ⊗ₜ[F] a := rfl

theorem jv_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    jv v (Formalism.UG.sigR σ (v.adicCompletion F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (jv v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b => rfl

theorem jv_inclE (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    jv v (Formalism.UG.inclE (F := F) (v.adicCompletion F) e) = jv v 1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e := by
  show jv v (e ⊗ₜ[F] 1) = jv v (1 ⊗ₜ[F] 1) * ((1 : AF F) ⊗ₜ[F] e)
  rw [jv_tmul, jv_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def backT : AF F ⊗[F] E →+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

end Place

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

structure SplitAt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) where
  sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, sp (Formalism.UG.sigR σ (v.adicCompletion F) x) = swapR _ (sp x)
  alg : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)

variable {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

def J1 (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  J.map ((RingHom.fst _ _).comp (s.sp.toRingHom.comp
    (Formalism.UG.inclE (F := F) (v.adicCompletion F))))

theorem J_split (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J i j) = J j i) :
    J.map (s.sp.toRingHom.comp (Formalism.UG.inclE (F := F) (v.adicCompletion F))) =
      splitJ (J1 s J) := by
  refine Matrix.ext fun i j => Prod.ext rfl ?_
  show (s.sp (Formalism.UG.inclE (F := F) _ (J i j))).2 = (s.sp (Formalism.UG.inclE (F := F) _ (J j i))).1
  have h := congrArg Prod.fst (s.sig (Formalism.UG.inclE (F := F) _ (J i j)))
  rw [← hJ i j]
  exact h.symm

theorem split_matrix_det_unit (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) : IsUnit (J1 s J).det := by
  have := RingHom.map_det ((RingHom.fst _ _).comp (s.sp.toRingHom.comp
    (Formalism.UG.inclE (F := F) (v.adicCompletion F)))) J
  rw [RingHom.mapMatrix_apply] at this
  rw [J1, ← this]
  exact (isUnit_iff_ne_zero.2 h).map _

def e1 (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) :
    UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J)) ≃* GL (Fin n) (v.adicCompletion F) :=
  Classical.choose (Formalism.UG.Final.SplitIso (v.adicCompletion F) (Fin n) (J1 s J) (split_matrix_det_unit s J h))

def locH (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) :
    GL (Fin n) (v.adicCompletion F) →* GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
  (bc s.sp.symm.toRingHom).comp
    ((UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J))).subtype.comp (e1 s J h).symm.toMonoidHom)

theorem locH_mem (s : SplitAt σ v) (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J i j) = J j i)
    (h : J.det ≠ 0) (a) : locH s J h a ∈ Formalism.UG.UPts σ J (v.adicCompletion F) := by
  have hc : s.sp.toRingHom.comp (Formalism.UG.sigR σ (v.adicCompletion F)) =
      (swapR (v.adicCompletion F)).comp s.sp := RingHom.ext s.sig
  have k : (⇑s.sp.symm.toRingHom ∘
      ⇑(s.sp.toRingHom.comp (Formalism.UG.inclE (F := F) (v.adicCompletion F)))) =
      ⇑(Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)) := by
    funext x; simp
  have key : ∀ x ∈ UJ (swapR (v.adicCompletion F)) (splitJ (J1 s J)),
      bc s.sp.symm.toRingHom x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) := by
    intro x hx
    have h1 := Formalism.UG.P.transport_bc_mem (swapR (v.adicCompletion F)) (Formalism.UG.sigR σ (v.adicCompletion F))
      s.sp.symm.toRingHom (Formalism.UG.P.transport_symm_comp _ _ s.sp hc) (splitJ (J1 s J)) x hx
    rw [← J_split s J hJ, Matrix.map_map, k] at h1
    exact h1
  exact key _ ((e1 s J h).symm a).2

end Local

section Emb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_herm' (V : HSp D) (i j : Fin V.rank) : D.sp.cm.sig (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

abbrev SplitD (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) := SplitAt D.sp.cm.sig v

variable {v : HeightOneSpectrum (𝓞 D.host.F)}

abbrev locV (V : HSp D) (s : SplitD D v) := locH s V.gram (Formalism.L2.Theta.gram_det_ne V)

theorem jv_J (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (V.gram.map (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F))).map (jv (E := D.host.E) v) =
      jv (E := D.host.E) v 1 • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) V.gram := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR]
  exact jv_inclE v _

theorem embV_mem (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    extGL (jv v) (locV V s a) ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  extGL_mem (jv v) (Formalism.UG.sigR D.sp.cm.sig _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (jv_sig _ v) _ _
    (jv_J V v) _ (locH_mem s V.gram (gram_herm' V) _ a)

def embV (V : HSp D) (s : SplitD D v) : GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V :=
  MonoidHom.codRestrict ((extGL (jv v)).comp (locV V s)) (HR (AF D.host.F) D.sp.cm.sig V.gram) (embV_mem V s)

theorem embV_coe (V : HSp D) (s : SplitD D v) (a : GL (Fin V.rank) (v.adicCompletion D.host.F)) :
    (matHom V (embV V s a)).val = extM (jv v) (locV V s a).val := rfl

theorem infHom_entry (V : HSp D) (g : GA D V) (i j : Fin V.rank) :
    (infHom V g).val i j = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((matHom V g).val i j) := rfl

theorem compV_entry (V : HSp D) (w : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (i j : Fin V.rank) :
    (compV V w g).val i j = Formalism.UG.prV w (backT ((matHom V g).val i j)) := rfl

end Emb

section Level

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def compVH (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GA D V →* GL (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
  (Formalism.UG.bc (Formalism.UG.prV v)).comp (Formalism.IndefR.Lev.finE V)

theorem compVH_apply (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : compVH V v g = compV V v g := rfl

end Level

end Formalism.IndefR.NX
