import Formalism.LocalRingCardinality.Lemmas
import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

def locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w B x}
  add_mem' := by
    rintro a b ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h1
    · rw [mul_smul]; exact B.smul_mem _ h2
  zero_mem' := ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := by
    rintro r a ⟨s, hs, h1⟩
    exact ⟨s, hs, by rw [smul_comm]; exact B.smul_mem r h1⟩

theorem mem_locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) (x : V) : x ∈ locS w B ↔ InLoc w B x := Iff.rfl

variable [Module K V] [IsScalarTower (𝓞 K) K V]

end Gen

variable {D : D7} (c : LatCmp D)

structure NuData (c : LatCmp D) where
  S : ℕ → Prop
  S_fin : {p | S p}.Finite
  NPf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn

  exists_residueChar_pow_smul_mem : ∀ u w hg, ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NPf u w hg

  T_abs : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

variable {c} (N : NuData c)

theorem int_mem_intW (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

def atT (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | D.nuIn u x ∈ LT.Nlam D u w}
  add_mem' := by
    intro a b ha hb
    show D.nuIn u (a + b) ∈ LT.Nlam D u w
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show D.nuIn u 0 ∈ LT.Nlam D u w
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show D.nuIn u (r • a) ∈ LT.Nlam D u w
    rw [← algebraMap_smul D.what₂.LL r a, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, int_mem_intW w r⟩ : intW D.what₂.places w) ha

include N in

def srv (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | c.cmpN u w hg x ∈ N.NPf u w hg}
  add_mem' := by
    intro a b ha hb
    show c.cmpN u w hg (a + b) ∈ N.NPf u w hg
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show c.cmpN u w hg 0 ∈ N.NPf u w hg
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show c.cmpN u w hg (r • a) ∈ N.NPf u w hg
    obtain ⟨o, ho⟩ := (c.embW_val u w hg _).1 ((D.plEq w).valuation_le_one r)
    rw [← algebraMap_smul D.what₂.LL r a, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o ha

def cond (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  if D.what₂.places.resChar w = (D.mem u).A.T then atT u w
  else if h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧ N.S (D.what₂.places.resChar w) then srv N u w h.1
  else locS (D.plEq w) (DV.MramL D u)

variable (hspan : ∀ u, Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤)

end Formalism.BasicNotions.Examples₂.NZ
