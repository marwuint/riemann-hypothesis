import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernel

noncomputable section

section Col

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct

namespace GlobalTheory.FamTraceChiCol.ColRead

theorem lamJ_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {gp : Fin 2 → ℕ} (G : Formalism.L2.Forms.GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    {w : HeightOneSpectrum (𝓞 E)} (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v)
    (hres : ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
        ∃ hh : G.phi i v h (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
          IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hh⟩ = ρ c)
    {xa : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)} (hA : IsRed w xa A)
    (χ : ℕ → MulChar (Formalism.L2.Forms.kv F v) ℂ) (k t : ℕ) (z : 𝓞 E)
    (hz : Ideal.Quotient.mk w.asIdeal z =
      ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < k ∧ (y : ℕ) ≠ k then A x y else 0)
    (fr : GL (Fin n) (v.adicCompletion F)) (hfr : fr = 1) :
    ∃ w' : v.adicCompletionIntegers F, (w' : v.adicCompletion F) = G.phi i v h ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∧
      Formalism.L2.Forms.lamJ (G.psi0 i v h) χ k t 0 k (Formalism.L2.Forms.redM F v (G.mat i v h fr (bc (prV (E := E) v) xa))) =
        G.psi0 i v h (IsLocalRing.residue _ w') := by
  subst hfr
  obtain ⟨hh, e⟩ := hres (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z : E)) _ (by rw [adAt_inclE]; exact hasRes_coe w z)
  refine ⟨⟨_, hh⟩, rfl, ?_⟩
  rw [e, TC.GLev0.redM_mat G i h ρ hres hA, Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one, hz, map_sum ρ]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [map_sum ρ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_ite ρ, map_zero]
  rfl

end GlobalTheory.FamTraceChiCol.ColRead

end Col

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol.ColRead

open GlobalTheory.SymBridge GlobalTheory.RootEx

set_option maxHeartbeats 1000000 in

theorem exists_close {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : Matrix (Fin n) (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A)
    (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : (mt V x).map q.pr = F.β * g.val * F.γ) :
    ∃ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z =
        (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) + 1 = b ∧ (b : ℕ) < κ ∧ (b : ℕ) ≠ κ then A a b else 0) ∧
      valuation k ((∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then g.val (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b)) else 0) -
        (ofSplit q).pr (z : D.host.E)) < 1 := by
  subst hr
  subst hn
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  have he' : ∀ a : Fin V.rank, e (Sum.inl (Sum.inl a)) = a := fun a => Fin.ext (he _)
  have hc : ∀ a b : Fin V.rank, ((a : ℕ) + 1 = b ∧ (b : ℕ) < V.rank ∧ (b : ℕ) ≠ V.rank) ↔ b.val = a.val + 1 := fun a b =>
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, b.2, b.2.ne⟩⟩
  refine ⟨∑ a : Fin V.rank, ∑ b : Fin V.rank, if b.val = a.val + 1 then R a b else 0, ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [apply_ite (Ideal.Quotient.mk PP.asIdeal), map_zero, hR]
    exact if_congr (hc a b).symm rfl rfl
  · let φ : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)
    have hφ : ∀ r : 𝓞 D.host.E, (ofSplit q).pr (r : D.host.E) = φ r := fun _ => rfl
    rw [hφ, map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => ?_
    rw [map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · rw [hgM, he', he']
      exact hM a b
    · rw [map_zero, sub_zero, map_zero]
      exact zero_lt_one

end GlobalTheory.FamTraceChiCol.ColRead

end
