import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def nfGen (q n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) (i : Fin c) : Sp E (n + c) :=
  ((q : E) ^ e i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)

def nfLat (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) : Set (Sp E (n + c)) :=
  {y | ∃ l ∈ stdAt E n P, ∃ s : Fin c → E, (∀ i, IntAt P (s i)) ∧
    y = Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i}

end Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks}

variable (Pr) in

def NF (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)),
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧
    z ∈ stdAt X.E (R.N j) P ∧
    h '' (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z

variable (Pr) in

def Sandwich (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ∃ y ∈ lamYat (Pr := Pr) (R := R) j P, h y = x) ∧
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P

variable (Pr R) in

def InclAt : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h k : AutY X R j, NF Pr j P h →
    k ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) → Sandwich Pr j P (h * k)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

theorem mem_lamYat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (y : Sp X.E (R.N j + cOf R j)) :
    y ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (y l) := by
  unfold lamYat LocE.lamY LocE.sclLat stdAt
  rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice]
  simp [LocE.scE]

theorem nf_one (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) : NF (R := R) Pr j P 1 := by
  refine ⟨0, 0, fun i => ⟨by simp, le_rfl⟩, zero_mem _, ?_⟩
  have key : ∀ (l : Sp X.E (R.N j)) (s : Fin (cOf R j) → X.E) (p : Fin (R.N j + cOf R j)),
      (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) 0 0 i :
        Sp X.E (R.N j + cOf R j)) p =
        Fin.addCases (motive := fun _ => X.E) l s p := by
    intro l s p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have : ∀ i : Fin (cOf R j), ¬ (a.1 = R.N j + i.1) := fun i => by omega
      simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, this]
    · simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, Fin.val_inj]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, ?_⟩
    funext p
    rw [key]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p <;> simp
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨_, fun p => ?_, rfl⟩
    have hk := key l s p
    rw [Pi.add_apply] at hk
    rw [hk]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simpa using (mem_localization_standardLattice _ _).1 hl a
    · simpa using hs b

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm
