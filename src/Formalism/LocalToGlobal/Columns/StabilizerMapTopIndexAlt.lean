import Formalism.LocalToGlobal.Columns.RecChainYKmap
import Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

variable (sel mu) in

structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet X.E (R.N R.m - 1) ∅ SG'), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

def tilPtY (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : PtY W cst (L₀.withTop m2 Λt Θt) u m2 R.m (topIdx L₀ m2 Λt Θt hm) :=
  ⟨(⟨(tilR hSG u d, fun P => F.fr P d), fun P x => F.spec P d x⟩, Set.univ), by
    classical
    show Set.univ ∈ (if R.m = m2 + 1 then ybSet sel mu cst (tilR hSG u d).1.N else {Set.univ})
    rw [if_neg (by omega)]
    rfl⟩

theorem tilPtY_deco (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : (tilPtY W cst L₀ u m2 Λt Θt hSG hm F d).deco = tilR hSG u d := rfl

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

def extYg (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    ((Formalism.L2.Col.chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G :=
  ((extR R hSG (s.1, s.2.1)).1, ⟨(extR R hSG (s.1, s.2.1)).2, hL s.2⟩,
    ⟨fun P => ⟨(F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d,
      frame_move (F.spec P _) (F.spec P _) (localization_tilR_fixed hPr hpi hs P.1)⟩,
      fun P _ => hQ d s hs P _⟩)

theorem extYg_fst (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM F)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs).1 = (extR R hSG (s.1, s.2.1)).1 := rfl

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

end Top

end Formalism.L2.Col.Sc.Fr
