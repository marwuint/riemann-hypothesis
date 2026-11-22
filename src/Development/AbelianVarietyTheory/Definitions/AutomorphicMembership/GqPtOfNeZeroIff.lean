import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P

def normOf (P : Matrix (Fin n) (Fin (r + 1)) E) : E := -pairM σ J P P (Fin.last r) (Fin.last r)

open scoped Classical in

def nullPt (T T' : E) (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w : Formalism.MainNotions.S.Point E (r + 1), Gq σ T T' (Formalism.MainNotions.S.ptMat w) = 0 then h.choose else onePt E r

open scoped Classical in

def ptOrNull (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if ∃ w, LiesAt w Z then ptOfMat Z else nullPt σ T T' r

variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

def mk (c : Col σ J P) (A : Matrix (Fin n) (Fin (r + 1)) E) (h : admitted σ J T' g c.lat P A) : Term σ J T' g P :=
  ⟨c, Quot.mk _ ⟨A, h⟩⟩

variable (t : Term σ J T' g P)

def col : Col σ J P := t.1

def lat : Submodule (𝓞 E) (Fin n → E) := t.col.lat

def fr : Matrix (Fin n) (Fin (r + 1)) E := (Quot.out t.2).1

def Zhat : Matrix (Fin (r + 1)) (Fin (r + 1)) E := pairM σ J t.fr P

def G : E := Gq σ (normOf σ J P) T' t.Zhat

def isId : Prop := ∃ h : admitted σ J T' g t.col.lat P P, t = mk t.col P h

def inS : Prop := Unip P t.fr

def FeqF : Prop := Move σ J t.lat P P t.fr

def relevant : Prop := Relevant σ J P t.fr

def M : Submodule (𝓞 E) (Fin n → E) := defLat g t.lat P t.fr

def BBne (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) : Prop := DefectAt F t.M t.lat p

def prim : Prop := PrimIn t.M t.lat

def generic : Prop := t.G ≠ 0 ∧ PrimIn t.M t.lat

def At (w : Formalism.MainNotions.S.Point E (r + 1)) : Prop := LiesAt w t.Zhat

def ptOf : Formalism.MainNotions.S.Point E (r + 1) := ptOrNull σ (normOf σ J P) T' t.Zhat

def Rep (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  Transp σ J P t.lat t.fr Λ A

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}

theorem Col.lat_mem (c : Col σ J P) : c.lat ∈ FrameLats σ J P := (Quot.out c).2

theorem Col.existsUnique (hJ : IsUnit J.det) (h : Λ ∈ FrameLats σ J P) :
    ∃! c : Col σ J P, ∃ s, InS σ J P s ∧ latMap s Λ = c.lat := by
  have hre : Equivalence fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1 :=
    ⟨fun _ => ⟨1, inS_one, latMap_one _⟩, fun ⟨s, hs, e⟩ => ⟨s⁻¹, inS_inv hJ hs, by
      rw [← e, ← latMap_mul, Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1), latMap_one]⟩,
      fun ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨t * s, inS_mul ht hs, by rw [latMap_mul, e, f]⟩⟩
  refine ⟨Quot.mk _ ⟨Λ, h⟩,
    hre.eqvGen_iff.1 (Quot.eq.1 (Quot.out_eq (Quot.mk _ (⟨Λ, h⟩ : FrameLats σ J P))).symm), fun c hc => ?_⟩
  exact (Quot.out_eq c).symm.trans (Quot.sound (a := (⟨Λ, h⟩ : FrameLats σ J P)) hc).symm

namespace Term

variable (t : Term σ J T' g P)

theorem lat_mem : t.lat ∈ FrameLats σ J P := t.col.lat_mem

theorem adm : admitted σ J T' g t.lat P t.fr := (Quot.out t.2).2

theorem mk_fr : mk t.col t.fr t.adm = t := by
  obtain ⟨c, q⟩ := t
  exact congrArg (Sigma.mk c) (Quot.out_eq q)

theorem mk_eq_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) (hB : admitted σ J T' g c.lat P B) :
    mk c A hA = mk c B hB ↔ Move σ J c.lat P A B := by
  have hre : Equivalence fun A B : {A // admitted σ J T' g c.lat P A} => Move σ J c.lat P A.1 B.1 :=
    (move_equivalence hJ).comap Subtype.val
  exact ⟨fun h => hre.eqvGen_iff.1 (Quot.eq.1 (eq_of_heq (Sigma.mk.inj h).2)),
    fun h => congrArg (Sigma.mk c) (Quot.sound h)⟩

theorem move_fr_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    Move σ J c.lat P (mk c A hA).fr A :=
  (mk_eq_mk hJ c (mk c A hA).adm hA).1 (mk c A hA).mk_fr

theorem rep_mk (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    (mk c A hA).Rep c.lat A := (move_fr_mk hJ c hA).transp hP

theorem exists_rep (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (h : Λ ∈ FrameLats σ J P)
    (hA : admitted σ J T' g Λ P A) : ∃ t : Term σ J T' g P, t.Rep Λ A := by
  obtain ⟨c, ⟨s, hs, e⟩, -⟩ := Col.existsUnique hJ h
  have k : Transp σ J P Λ A c.lat (s * A) := ⟨s, hs, e, 1, one_mem_UO, (Matrix.mul_one _).symm⟩
  exact ⟨_, (rep_mk hJ hP c (k.adm hJ hP.1 h.2 c.lat_mem.2 hA)).trans (k.symm hJ)⟩

variable {t}

variable (t)

theorem generic_iff : t.generic ↔ t.G ≠ 0 ∧ t.prim := Iff.rfl

end Term

end Basic

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

def spFrame (S : Spaces R F E) (c : E) : Matrix (Fin (S.Y 0).rank) (Fin (R.rS + 1)) E :=
  coMat (S.Y 0) (Fin.snoc (α := fun _ => (S.Y 0).V) S.hypE (c • S.zm))

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def recFrame (u : D.what₂.Word) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.R.rS + 1)) D.host.E :=
  spFrame D.sp (D.cOf u)⁻¹

abbrev RecTerm (u u' : D.what₂.Word) : Type :=
  Term (starRingEnd D.host.E) (D.sp.Y 0).gram (((D.mem u').A.T : ℕ) : D.host.E) (D.host.g 0 * D.host.g 1)
    (recFrame D u)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
