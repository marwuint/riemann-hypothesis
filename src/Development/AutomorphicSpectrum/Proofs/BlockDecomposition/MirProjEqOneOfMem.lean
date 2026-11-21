import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      GlobalTheory.BZMir.eLast k n j :=
    fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
  have hblock : ∀ i j : Fin n,
      ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
        (1 : Matrix (Fin n) (Fin n) k) i j :=
    fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hy
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
  apply Units.ext
  ext i j
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
  rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
      GlobalTheory.BZMir.eLast]
  · simp [hrow, GlobalTheory.BZMir.eLast]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
