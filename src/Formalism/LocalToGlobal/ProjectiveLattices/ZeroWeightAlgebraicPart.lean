import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

theorem rdU_one_of (h : LawsP T) {j : ℕ} (hj : InR D j) (k : (T.U j T.σ₀).Comp)
    {y : Frame ((T.U j T.σ₀).X k).Ψ D.R.r} (hy : y ∈ ((T.U j T.σ₀).X k).dom) : rdU (T.U j T.σ₀) 1 k y = 1 := by
  haveI : IsReduced (CAt T.σ₀) := inferInstanceAs (IsReduced ℂ)
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
  show toC (evalAt (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) 1
    ((T.U j T.σ₀).un k ⟨y, hy⟩)) = 1
  rw [evalAt_one (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) _
    (h.allTest j hj _ _)]
  rfl

open Classical in

def frAt {j : ℕ} {k : (T.U j T.σ₀).Comp} (x₀ x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    Frame ((T.U j T.σ₀).X k).Ψ D.R.r :=
  if x ∈ ((T.U j T.σ₀).X k).dom then x else x₀

theorem frAt_mem {j : ℕ} {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) :
    frAt x₀ x ∈ ((T.U j T.σ₀).X k).dom := by
  unfold frAt
  split_ifs with hx
  · exact hx
  · exact hx0

def evFr (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) : T.R j →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) where
  toFun f x := rdU (T.U j T.σ₀) f k (frAt x₀ x)
  map_one' := funext fun x => rdU_one_of h hj k (frAt_mem hx0 x)
  map_mul' f g := funext fun x => by
    show rdU (T.U j T.σ₀) (f * g) k (frAt x₀ x) = rdU (T.U j T.σ₀) f k (frAt x₀ x) * rdU (T.U j T.σ₀) g k (frAt x₀ x)
    rw [rdU_mul]; rfl
  map_zero' := funext fun x => by simp
  map_add' f g := funext fun x => by simp

def augF {j : ℕ} (k : (T.U j T.σ₀).Comp) :
    AddMonoidAlgebra (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id _) 1 (fun _ _ => Commute.all _ _)

def thR (h : LawsP T) {j : ℕ} (hj : InR D j) {k : (T.U j T.σ₀).Comp} {x₀ : Frame ((T.U j T.σ₀).X k).Ψ D.R.r}
    (hx0 : x₀ ∈ ((T.U j T.σ₀).X k).dom) :
    AddMonoidAlgebra (T.R j) (WTZ D.host.E) →+* (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  (augF k).comp (AddMonoidAlgebra.mapRingHom (WTZ D.host.E) (evFr h hj hx0))

def secZ (T : Top D) (j : ℕ) (G : WTZ D.host.E) : Submodule T.Q.c.F (T.R j) :=
  ⨆ u : {u : WeightFamilies.Wt D j // wtZ (wtA u) u.n = G}, sec (T.Q.Xo j) T.Q.c (wtA u.1) u.1.n

theorem secZ_mul {j : ℕ} {G G' : WTZ D.host.E} {f g : T.R j} (hf : f ∈ secZ T j G) (hg : g ∈ secZ T j G') :
    f * g ∈ secZ T j (G + G') := by
  refine Submodule.iSup_induction _ (motive := fun f => f * g ∈ secZ T j (G + G')) hf (fun p f hf => ?_)
    (by rw [zero_mul]; exact zero_mem _) (fun f1 f2 h1 h2 => by rw [add_mul]; exact add_mem h1 h2)
  refine Submodule.iSup_induction _ (motive := fun g => f * g ∈ secZ T j (G + G')) hg (fun q g hg => ?_)
    (by rw [mul_zero]; exact zero_mem _) (fun g1 g2 h1 h2 => by rw [mul_add]; exact add_mem h1 h2)
  have hs := sec_mul (T.Q.Xo j) T.Q.c _ _ _ _ hf hg
  rw [← wtA_wadd] at hs
  refine Submodule.mem_iSup_of_mem ⟨WeightAlgebra.wadd p.1 q.1, ?_⟩ hs
  show wtZ (wtA (WeightAlgebra.wadd p.1 q.1)) (p.1.n + q.1.n) = G + G'
  rw [wtA_wadd, wtZ_add, p.2, q.2]

def w00 (D : D7) (j : ℕ) : WeightFamilies.Wt D j := WeightAlgebra.wscalar D j 0 ⟨0, rfl⟩

theorem zero_weight_algebraic_part {j : ℕ} : wtA (w00 D j) = 0 := by
  funext x
  simp [wtA, w00, WeightAlgebra.wscalar, ext0]

theorem one_mem_sec {j : ℕ} : (1 : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA (w00 D j)) (w00 D j).n := by
  rw [zero_weight_algebraic_part]
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1; rw [map_one]
  · show (1 : p.R) = wchar (ex (T.Q.Dw j) 0 0) t * 1
    have : ex (T.Q.Dw j) 0 0 = 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem zero_weight_exponent_zero {j : ℕ} : wtZ (wtA (w00 D j)) (w00 D j).n = 0 := by
  rw [zero_weight_algebraic_part]
  rfl

def secSub (T : Top D) (j : ℕ) : Subring (AddMonoidAlgebra (T.R j) (WTZ D.host.E)) where
  carrier := {b | ∀ G, b.coeff G ∈ secZ T j G}
  one_mem' G := by
    classical
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hG0
    · subst hG0
      exact Submodule.mem_iSup_of_mem ⟨w00 D j, zero_weight_exponent_zero⟩ one_mem_sec
    · exact zero_mem _
  mul_mem' {a b} ha hb G := by
    classical
    rw [AddMonoidAlgebra.coeff_mul]
    refine Submodule.finsuppSum_mem _ _ _ _ fun m1 _ => Submodule.finsuppSum_mem _ _ _ _ fun m2 _ => ?_
    split_ifs with hm
    · subst hm; exact secZ_mul (ha m1) (hb m2)
    · exact zero_mem _
  zero_mem' G := by simp
  add_mem' {a b} ha hb G := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (ha G) (hb G)
  neg_mem' {a} ha G := by
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]; exact neg_mem (ha G)

end Formalism.L2.Pj
