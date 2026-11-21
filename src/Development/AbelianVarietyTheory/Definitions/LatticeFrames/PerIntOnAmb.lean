import Mathlib
import Formalism.LocalRingCardinality.DataAmbForm

noncomputable section

namespace GlobalTheory.Core.Int

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7) (u : D.what₂.Word)

def ValGe (w : D.what₂.places.Pl) (z : ℂ) (s : ℝ) : Prop :=
  ∃ y : D.what₂.LL, D.what₂.embLL y = z ∧ (y = 0 ∨ s ≤ (vAdd (D.plEq w) y : ℝ))

def vGam (w : D.what₂.places.Pl) : ℝ :=
  (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ)

def PairInt (w : D.what₂.places.Pl) : Prop :=
  ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier,
    ValGe D w ((D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F))
      (-((D.what₂.places.ramIdx w : ℝ) * vGam D u w))

def ColGe (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V) (s : ℝ) : Prop :=
  ∃ y : ((D.fm u).lat D.R.m).V, (D.fm u).emb D.R.m y = (D.mem u).C.col ((D.fm u).emb 0 x) ∧
    ∃ (a : D.what₂.LL) (z : ((D.fm u).lat D.R.m).V), z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L ∧ y = a • z ∧
      (a = 0 ∨ (D.what₂.places.ramIdx w : ℝ) * s ≤ (vAdd (D.plEq w) a : ℝ))

def shift (S : Finset D.what₂.places.Pl) (n : D.what₂.places.Pl → ℤ) (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  Submodule.span (𝓞 D.what₂.LL)
    {x | ∃ a ∈ (∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w))),
      ∃ y ∈ N, x = (a : D.what₂.LL) • y}

end GlobalTheory.Core.Int
