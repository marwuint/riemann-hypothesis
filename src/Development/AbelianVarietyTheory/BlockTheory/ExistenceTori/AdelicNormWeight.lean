import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain
open scoped TensorProduct

section Adelic

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev Plc : Type := HeightOneSpectrum (𝓞 (maximalRealSubfield E))

abbrev AdF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)

def AdE : Type := AdF E ⊗[maximalRealSubfield E] E

instance : CommRing (AdE E) := inferInstanceAs (CommRing (AdF E ⊗[maximalRealSubfield E] E))

def adConj : (AdF E ⊗[maximalRealSubfield E] E) →ₐ[maximalRealSubfield E] (AdF E ⊗[maximalRealSubfield E] E) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IsCMField.complexConj E).toAlgHom

theorem adConj_adConj (x : AdF E ⊗[maximalRealSubfield E] E) : adConj E (adConj E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [adConj]
  | add x y hx hy => simp [hx, hy]

instance : StarRing (AdE E) where
  star x := adConj E x
  star_involutive x := adConj_adConj E x
  star_mul x y := by
    show adConj E (x * y) = adConj E y * adConj E x
    rw [mul_comm (adConj E y)]
    exact map_mul (adConj E) x y
  star_add x y := map_add (adConj E) x y

def diagE : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight (R := maximalRealSubfield E) (A := AdF E) (B := E)).toRingHom

def inclF : AdF E →+* AdE E :=
  Algebra.TensorProduct.includeLeftRingHom (R := maximalRealSubfield E) (A := AdF E) (B := E)

def intAd : Subring (AdE E) :=
  Subring.closure ((inclF E '' {a | ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)}) ∪
    Set.range fun o : 𝓞 E => diagE E (o : E))

abbrev UA (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) (AdE E)

variable {E} {n : ℕ}

def ptsIn (n : ℕ) (R : Subring (AdE E)) : Subgroup (UA E n) where
  carrier := {k | (∀ a b, k.1 a b ∈ R) ∧ ∀ a b, (k⁻¹).1 a b ∈ R}
  one_mem' := by
    have : ∀ a b : Fin n, (1 : UA E n).1 a b ∈ R := fun a b => by
      show (1 : Matrix (Fin n) (Fin n) (AdE E)) a b ∈ R
      rw [Matrix.one_apply]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    exact ⟨this, by rw [inv_one]; exact this⟩
  mul_mem' := by
    have key : ∀ x y : UA E n, (∀ a b, x.1 a b ∈ R) → (∀ a b, y.1 a b ∈ R) → ∀ a b, (x * y).1 a b ∈ R :=
      fun x y hx hy a b => by
        show (x.1 * y.1) a b ∈ R
        rw [Matrix.mul_apply]
        exact R.sum_mem fun j _ => R.mul_mem (hx a j) (hy j b)
    intro x y hx hy
    exact ⟨key x y hx.1 hy.1, by rw [mul_inv_rev]; exact key _ _ hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable (E) in

def ratPts (n : ℕ) : Subgroup (UA E n) := ptsIn n (diagE E).range

def latOf (h : UA E n) : GenLat E n where
  La :=
  { carrier := {x | ∃ u : Fin n → AdE E, (∀ b, u b ∈ intAd E) ∧ ∀ a, diagE E (x a) = ∑ b, star (h.1 a b) * u b}
    zero_mem' := ⟨0, fun _ => (intAd E).zero_mem, fun a => by simp⟩
    add_mem' := by
      rintro x y ⟨u, hu, hx⟩ ⟨w, hw, hy⟩
      refine ⟨u + w, fun b => (intAd E).add_mem (hu b) (hw b), fun a => ?_⟩
      simp [hx a, hy a, mul_add, Finset.sum_add_distrib]
    smul_mem' := by
      rintro o x ⟨u, hu, hx⟩
      refine ⟨fun b => diagE E (o : E) * u b,
        fun b => (intAd E).mul_mem (Subring.subset_closure (Or.inr ⟨o, rfl⟩)) (hu b), fun a => ?_⟩
      have : (o • x) a = (o : E) * x a := rfl
      rw [this, map_mul, hx a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring }

def normH (r : ℕ) (h : UA E n) : ℕ :=
  ((latOf h).Ln.toAddSubgroup.addSubgroupOf (latOf h).La.toAddSubgroup).index ^ r

end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def fourierSum {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → ConjQ Dw l, ph x * zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)))

def IsScalar {n : ℕ} (ep : UA E n → ℂ) (h : UA E n) (κ : c.F) : Prop :=
  (κ : ℂ) = ep h * (((Real.sqrt (normH (Dw.p + Dw.q) h : ℝ))⁻¹ : ℝ) : ℂ)

variable {Xo c} in

def coverDatum {n : ℕ} (d : DeltaDat Xo c n) (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F) :
    (Fin n → ConjQ Dw d.l₂) → d.c₂.F :=
  fun x => d.eF (ph (fun b => Submodule.Quotient.mk (qRep (x b))) * phδ (fun b => Submodule.Quotient.mk (qRep (x b))))

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
