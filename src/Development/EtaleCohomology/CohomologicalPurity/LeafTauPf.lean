import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem cast_inj {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Function.Injective (Ht.cast (q := q) (E := E) h1 h2) := by
  subst h1; subst h2; intro a b h; exact h

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast (q := q) (E := E) h1 h2 0 = 0 := by
  subst h1; subst h2; rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n) (h4 : i' = i)
    (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = a := by
  subst h1; subst h2; rfl

def LeafTauU : Prop := LeafPB → LeafTail → Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R],
  IsUnit (q : R) → ∀ n i : ℤ, Function.Bijective (poly q (d + 1) 1 R d n i)

def LeafTauLin : Prop := ∀ (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a b,
  poly q N k R m n i (a - b) = poly q N k R m n i a - poly q N k R m n i b

def LeafTauFgt : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P : Arrow Spc) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.fgt q P _ _ (Hs.act q a b) = cup q a (Hs.fgt q P _ _ b)

def LeafTauTop : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (n i : ℤ) (x : Ht q (sp R) n i)
  (a : ∀ j : Fin d, Ht q (sp R) (2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) ((d : ℤ) - ((j : ℕ) : ℤ))),
  ∃ e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)),
    e (Fin.last d) = x.cast (by simp) (by simp) ∧
    cup q (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ x)
      (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a) =
      poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) e

theorem cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a b : Ht q E n i) :
    Ht.cast h1 h2 (a - b) = Ht.cast h1 h2 a - Ht.cast h1 h2 b := by
  subst h1; subst h2; rfl

theorem tauLin : LeafTauLin := by
  intro q N k R _ m n i a b
  unfold poly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.sub_apply, map_sub, map_sub, AddMonoidHom.sub_apply, cast_sub]

theorem tauFgt : LeafTauFgt := by
  intro h q _ P n m i j a b
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change pull _ (dbl.inl P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _
    (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q a (pull _ (dbl.inl P) _ _ b.1)
  rw [map_sub, (h q).1, (h q).1, hb, map_zero, map_zero, map_zero, sub_zero, ← pull_comp, inl_fold, pull_id]

theorem poly_zero (hL : LeafTauLin) (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) :
    poly q N k R m n i 0 = 0 := by
  have h := hL q N k R m n i 0 0
  rw [sub_zero, sub_self] at h
  exact h

end LateralTheory.CohomologicalPurity.Thom
