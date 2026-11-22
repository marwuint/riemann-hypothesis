import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic

namespace GlobalTheory.FlagZ

section Minor

variable {N : ℕ} {A B : Type} [CommRing A] [CommRing B]

abbrev Rows (N : ℕ) (l : Fin (N + 1)) : Type := Set.powersetCard (Fin N) l

def plDim (N : ℕ) (l : Fin (N + 1)) : ℕ := N.choose l - 1

theorem card_rows (N : ℕ) (l : Fin (N + 1)) : Fintype.card (Rows N l) = plDim N l + 1 := by
  rw [plDim, Nat.sub_add_cancel (Nat.choose_pos l.is_le), ← Nat.card_eq_fintype_card,
    Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

def rowsEquiv (N : ℕ) (l : Fin (N + 1)) : Rows N l ≃ Fin (plDim N l + 1) :=
  Fintype.equivFinOfCardEq (card_rows N l)

def minor (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) : A :=
  (g.submatrix (subsetEnum I) (Fin.castLE l.is_le)).det

def plVec (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) : Fin (plDim N l + 1) → A :=
  fun a => minor g l ((rowsEquiv N l).symm a)

@[simp] theorem plVec_rowsEquiv (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) :
    plVec g l (rowsEquiv N l I) = minor g l I := by simp [plVec]

theorem minor_map (ψ : A →+* B) (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) :
    minor (g.map ψ) l I = ψ (minor g l I) := (ψ.map_det _).symm

theorem span_plVec (g : GL (Fin N) A) (l : Fin (N + 1)) : Ideal.span (Set.range (plVec g.1 l)) = ⊤ := by
  have h := det_submatrix_mul_eq_sum_minors (g⁻¹).1 g.1 (Fin.castLE l.is_le) (Fin.castLE l.is_le)
  rw [Units.inv_mul, submatrix_one _ (Fin.castLE_injective _), det_one] at h
  rw [Ideal.eq_top_iff_one, h]
  exact Ideal.sum_mem _ fun I _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨rowsEquiv N l I, plVec_rowsEquiv _ _ _⟩)

theorem minor_mul (g b : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1))
    (hb : ∀ i j : Fin N, (j : ℕ) < l → (l : ℕ) ≤ i → b i j = 0) (I : Rows N l) :
    minor (g * b) l I = minor g l I * (b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  rw [minor, minor, ← det_mul]
  congr 1
  ext i j
  simp only [submatrix_apply, mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE l.is_le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
    fun _ => rfl).symm
  rw [hb k _ j.2 (not_lt.1 fun h => hk ⟨⟨k, h⟩, rfl⟩), mul_zero]

end Minor

section Ring

variable (ι : Type) [Fintype ι] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]

def genDet : MvPolynomial (ι × Fin N × Fin N) ℤ :=
  ∏ τ, (Matrix.of fun i j => MvPolynomial.X (τ, i, j)).det

variable {ι N} in

theorem eval₂_genDet (g : ι → Matrix (Fin N) (Fin N) A) :
    MvPolynomial.eval₂Hom (Int.castRingHom A) (fun x => g x.1 x.2.1 x.2.2) (genDet ι N) = ∏ τ, (g τ).det := by
  rw [genDet, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem genDet_ne_zero : genDet ι N ≠ 0 := fun h => by
  have := eval₂_genDet (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℤ))
  simp [h] at this

abbrev GLRing : Type := Localization.Away (genDet ι N)

instance : IsDomain (GLRing ι N) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (genDet_ne_zero ι N))

def univGL (τ : ι) : GL (Fin N) (GLRing ι N) :=
  GeneralLinearGroup.mk'' (Matrix.of fun i j => algebraMap _ _ (MvPolynomial.X (R := ℤ) (τ, i, j))) (by
    classical
    have h : IsUnit (algebraMap _ (GLRing ι N) (∏ τ, (Matrix.of fun i j => MvPolynomial.X (R := ℤ) (τ, i, j)).det)) :=
      IsLocalization.Away.algebraMap_isUnit (S := GLRing ι N) (genDet ι N)
    rw [map_prod] at h
    have := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) h
    rwa [RingHom.map_det] at this)

variable {ι N}

theorem univGL_apply (τ : ι) (i j : Fin N) :
    (univGL ι N τ).1 i j = algebraMap _ _ (MvPolynomial.X (R := ℤ) (τ, i, j)) := rfl

def evalGL (g : ι → GL (Fin N) A) : GLRing ι N →+* A :=
  IsLocalization.Away.lift (genDet ι N)
    (g := MvPolynomial.eval₂Hom (Int.castRingHom A) fun x => (g x.1).1 x.2.1 x.2.2) (by
      rw [eval₂_genDet fun τ => (g τ).1]
      exact IsUnit.prod_univ_iff.2 fun τ => (isUnit_iff_isUnit_det _).1 (g τ).isUnit)

theorem evalGL_X (g : ι → GL (Fin N) A) (x : ι × Fin N × Fin N) :
    evalGL g (algebraMap _ _ (MvPolynomial.X (R := ℤ) x)) = (g x.1).1 x.2.1 x.2.2 := by
  rw [evalGL, IsLocalization.Away.lift_eq, MvPolynomial.eval₂Hom_X']

theorem map_evalGL_univGL (g : ι → GL (Fin N) A) (τ : ι) :
    GeneralLinearGroup.map (evalGL g) (univGL ι N τ) = g τ := by
  ext i j
  rw [GeneralLinearGroup.map_apply, univGL_apply, evalGL_X]

end Ring

def toZ (X : Scheme.{0}) : X ⟶ Sp ℤ := specZIsTerminal.from X

theorem toZ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g := specZIsTerminal.hom_ext f g

section Part

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))
  {A B : Type} [CommRing A] [CommRing B]

abbrev Amb : Scheme.{0} := ∏ᶜ fun k => PSpace ℤ (plDim N (l k))

omit [Fintype ι] in

def plPt (g : ι → GL (Fin N) A) : Sp A ⟶ Amb l :=
  Pi.lift fun k => pt (Int.castRingHom A) (plVec (g (a k)).1 (l k)) (span_plVec _ _)

omit [Fintype ι] in

@[reassoc] theorem plPt_π (g : ι → GL (Fin N) A) (k : κ) :
    plPt a l g ≫ Pi.π _ k = pt (Int.castRingHom A) (plVec (g (a k)).1 (l k)) (span_plVec _ _) :=
  Pi.lift_π _ _

omit [Fintype ι] in

@[reassoc] theorem spMap_plPt (ψ : A →+* B) (g : ι → GL (Fin N) A) :
    spMap ψ ≫ plPt a l g = plPt a l fun τ => GeneralLinearGroup.map ψ (g τ) :=
  Pi.hom_ext _ _ fun k => by
    rw [Category.assoc, plPt_π, plPt_π, spMap_pt]
    congr 1
    · exact RingHom.ext_int _ _
    · exact funext fun c => (minor_map ψ _ _ _).symm

instance : QuasiCompact (plPt a l (univGL ι N)) := quasiCompact_of_noetherianSpace_source _

def Part : Scheme.{0} := (plPt a l (univGL ι N)).image

def plEmb : Part a l ⟶ Amb l := (plPt a l (univGL ι N)).imageι

instance : IsClosedImmersion (plEmb a l) :=
  inferInstanceAs (IsClosedImmersion (plPt a l (univGL ι N)).imageι)

instance : IsIntegral (Part a l) := isIntegral_image _

def orbit : Sp (GLRing ι N) ⟶ Part a l := (plPt a l (univGL ι N)).toImage

instance : IsSchemeTheoreticallyDominant (orbit a l) := schemeDominant_toImage _

def flagPt (g : ι → GL (Fin N) A) : Sp A ⟶ Part a l := spMap (evalGL g) ≫ orbit a l

@[reassoc] theorem flagPt_plEmb (g : ι → GL (Fin N) A) : flagPt a l g ≫ plEmb a l = plPt a l g := by
  rw [flagPt, Category.assoc]
  erw [Scheme.Hom.toImage_imageι]
  simp only [spMap_plPt, map_evalGL_univGL]

@[reassoc] theorem spMap_flagPt (ψ : A →+* B) (g : ι → GL (Fin N) A) :
    spMap ψ ≫ flagPt a l g = flagPt a l fun τ => GeneralLinearGroup.map ψ (g τ) := by
  rw [← cancel_mono (plEmb a l), Category.assoc, flagPt_plEmb, flagPt_plEmb, spMap_plPt]

theorem flagPt_univGL : flagPt a l (univGL ι N) = orbit a l := by
  rw [← cancel_mono (plEmb a l), flagPt_plEmb]
  exact (Scheme.Hom.toImage_imageι _).symm

theorem flagPt_eq_iff (g h : ι → GL (Fin N) A) : flagPt a l g = flagPt a l h ↔
    ∀ k, ∃ u : Aˣ, ∀ I, minor (h (a k)).1 (l k) I = u * minor (g (a k)).1 (l k) I := by
  rw [← cancel_mono (plEmb a l), flagPt_plEmb, flagPt_plEmb]
  refine ⟨fun e k => ?_, fun e => Pi.hom_ext _ _ fun k => ?_⟩
  · have := congrArg (· ≫ Pi.π _ k) e
    simp only [plPt_π] at this
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff _ _ _).1 this
    exact ⟨u, fun I => by simpa [Units.smul_def] using congrFun hu (rowsEquiv _ _ I)⟩
  · obtain ⟨u, hu⟩ := e k
    rw [plPt_π, plPt_π]
    exact (pt_eq_pt_iff _ _ _).2 ⟨u, funext fun c => hu _⟩

theorem flagPt_mul (g b : ι → GL (Fin N) A)
    (hb : ∀ k (i j : Fin N), (j : ℕ) < l k → (l k : ℕ) ≤ i → (b (a k)).1 i j = 0) :
    flagPt a l (g * b) = flagPt a l g := by
  refine ((flagPt_eq_iff a l _ _).2 fun k => ?_).symm
  have h (g : GL (Fin N) A) := minor_mul g.1 (b (a k)).1 (l k) (hb k)
  have hu : IsUnit ((b (a k)).1.submatrix (Fin.castLE (l k).is_le) (Fin.castLE (l k).is_le)).det := by
    refine Ideal.span_singleton_eq_top.1 (top_le_iff.1 ((span_plVec (b (a k)) (l k)).ge.trans ?_))
    refine Ideal.span_le.2 (Set.range_subset_iff.2 fun c => Ideal.mem_span_singleton.2 ?_)
    have := h 1 ((rowsEquiv _ _).symm c)
    rw [Units.val_one, one_mul] at this
    exact Dvd.intro_left _ this.symm
  exact ⟨hu.unit, fun I => (h _ I).trans (mul_comm _ _)⟩

abbrev str : Part a l ⟶ Sp ℤ := toZ _

end Part

section Cell

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1)) {A : Type} [CommRing A]

def Below (τ : ι) (i j : Fin N) : Prop := ∃ k, a k = τ ∧ (j : ℕ) < l k ∧ (l k : ℕ) ≤ i

abbrev CellVar : Type := {x : ι × Fin N × Fin N // Below a l x.1 x.2.1 x.2.2}

abbrev CellRing : Type := MvPolynomial (CellVar a l) ℤ

open Classical in

def lowMat (τ : ι) : Matrix (Fin N) (Fin N) (CellRing a l) :=
  Matrix.of fun i j => if h : Below a l τ i j then MvPolynomial.X ⟨(τ, i, j), h⟩ else (1 : Matrix _ _ _) i j

omit [Fintype ι] [Finite κ] in

theorem det_lowMat (τ : ι) : (lowMat a l τ).det = 1 := by
  have h {i j : Fin N} (hij : i ≤ j) : lowMat a l τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : (lowMat a l τ).BlockTriangular OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans (one_apply_ne (ne_of_lt (show i < j from hij)))
  rw [det_of_lowerTriangular _ ht]
  simp [h le_rfl]

def cellGL (w : ι → Equiv.Perm (Fin N)) (τ : ι) : GL (Fin N) (CellRing a l) :=
  GeneralLinearGroup.mk'' ((lowMat a l τ).submatrix (w τ) id) (by
    rw [det_permute, det_lowMat, mul_one]
    exact (Equiv.Perm.sign (w τ)).isUnit.map (Int.castRingHom _))

def cell (w : ι → Equiv.Perm (Fin N)) : Sp (CellRing a l) ⟶ Part a l := flagPt a l (cellGL a l w)

theorem flagPt_eq_comp_cell (w : ι → Equiv.Perm (Fin N)) (L b : ι → GL (Fin N) A)
    (hL : ∀ τ i j, ¬ Below a l τ (w τ i) j → (L τ).1 i j = (1 : Matrix _ _ A) (w τ i) j)
    (hb : ∀ τ i j, Below a l τ i j → (b τ).1 i j = 0) :
    flagPt a l (L * b) = spMap (MvPolynomial.eval₂Hom (Int.castRingHom A)
      fun x : CellVar a l => (L x.1.1).1 ((w x.1.1).symm x.1.2.1) x.1.2.2) ≫ cell a l w := by
  rw [flagPt_mul a l L b fun k i j h₁ h₂ => hb _ i j ⟨k, rfl, h₁, h₂⟩, cell, spMap_flagPt]
  congr 1
  ext τ i j
  rw [GeneralLinearGroup.map_apply]
  change _ = MvPolynomial.eval₂Hom _ _ (lowMat a l τ (w τ i) j)
  by_cases h : Below a l τ (w τ i) j
  · simp [lowMat, h]
  · by_cases e : w τ i = j
    · subst e
      simp [lowMat, h, hL τ i _ h]
    · simp [lowMat, h, hL τ i j h, e]

end Cell

section Full

open GlobalTheory.FlagPoly GlobalTheory.ArInt Formalism.DegreeFormula

variable (ι : Type) [Fintype ι] (N : ℕ)

abbrev Fl : Scheme.{0} := Part (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd

abbrev flStr : Fl ι N ⟶ Sp ℤ := str _ _

variable {ι N}

variable (ι N)

variable {ι N}

end Full

end GlobalTheory.FlagZ
