import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnityStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TwPlaces

theorem rou_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

theorem rou_inv {x : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ x⁻¹ ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  exact ⟨n, hn, by rw [inv_pow, hx, inv_one]⟩

theorem rou_prod {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ f i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, f i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact rou_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem rou_circle {x : Circle} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ (x : ℂ) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, hn, by rw [← Circle.coe_pow, hx, Circle.coe_one]⟩

theorem toLoc_frames {E k : Type} [Field E] [Field k] (ι : E →+* k) {A C : Type} [Fintype A] [Fintype C] {a b a' b' : ℕ}
    (ha : a' = a) (hb : b' = b) (e : C ≃ Fin b) (e' : A ≃ Fin a) (f' : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (f : (Fin b → E) ≃ₗ[E] (Fin b → E)) (z : Matrix (Fin b') (Fin a') E) (M : Matrix (Fin b') C k) (M' : Matrix (Fin a') A k)
    (hM : ∀ r c, ι (f (Pi.single (e c) 1) (finCongr hb r)) = M r c)
    (hM' : ∀ r c, ι (f' (Pi.single (e' c) 1) (finCongr ha r)) = M' r c) :
    M * (GlobalTheory.SymBridge.toLoc ι e e' (Formalism.L2.Col.inFr f' f (Matrix.toLin' (z.reindex (finCongr hb) (finCongr ha)))) : Matrix C A k) =
      z.map ι * M' := by
  subst ha hb
  have key : ∀ (y : Fin b' → E) r, ∑ c, M r c * ι (f.symm y (e c)) = ι (y r) := by
    intro y r
    have h4 : y = ∑ c, f.symm y (e c) • f (Pi.single (e c) 1) := by
      conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun b _ => map_smul _ _ _
    conv_rhs => rw [h4, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hM r c, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]
    rfl
  ext r c
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (key (Matrix.toLin' (z.reindex (finCongr rfl) (finCongr rfl)) (f' (Pi.single (e' c) 1))) r).trans ?_
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, ← hM' q c]
  rfl

theorem frame_cancel {k : Type} [Field k] {N N' : ℕ} {Y Y' : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    {T : Matrix Y Y' k} {z : Matrix (Fin N) (Fin N') k} {M : Matrix (Fin N') Y' k} (h : F.β * T = z * M) : T = F.γ * z * M := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

theorem isLocFac_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (hd : DenseRange (ofSplit q).pr) (ψ : AddChar (AF D.host.F) ℂ) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : ∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) (eT : ∀ z, z ∈ LT ↔ z ∈ intVec D T.rank)
    (fS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (fT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (c : WO S T →₀ ℂ) (Ξk : Matrix Y Y' k → ℂ) (hSB : Ξk ∈ SB (Matrix Y Y' k)) (hc : (ofSplit q).IsCombAt ψ FS FT c Ξk)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (hΞ : ∀ z, Ξ z = Ξk (FT.γ * z.map (ofSplit q).pr * FS.β)) :
    GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξ ∧ GlobalTheory.FinPl.CombAt (· = q.v) c :=
  ⟨⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ofSplit q, Y, Y', inferInstance, inferInstance, inferInstance,
    inferInstance, FS, FT, Ξk, hd, hq,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom D k q hU Y Y' S T FS FT LS LT hS hT eS eT fS fT, hSB, hc, hΞ⟩,
    fun u hu r s => (GlobalTheory.FinPl.FrameLat.idem_iff q _).2 (hc.1 u hu r s)⟩

theorem xiTop_mem_SB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (w : kˣ)
    (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) w) : T.xiTop (box _ w) ψ ν (-1) yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hv1 : valuation k (-1 : k) = 1 := by simp
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν (-1) hψ hν hv1 (X (s + 1)) 1 1 _ (cosetInd_mem_SB w yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

section Steps

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T} (J : QJ a t) (i : Fin J.r)

variable {J i}

theorem even_ranks (R : Ranks) (j : ℕ) (h : j + 2 < R.m) :
    Even (R.N j + Formalism.L2.Col.cOf R j + (R.N (j + 1 + 1) + Formalism.L2.Col.cOf R (j + 1 + 1))) := by
  obtain ⟨c, hc⟩ : ∃ c, R.m = j + 3 + c := ⟨R.m - (j + 3), by omega⟩
  have e1 : Formalism.L2.Col.cOf R j = c + 2 := by unfold Formalism.L2.Col.cOf; omega
  have e2 : Formalism.L2.Col.cOf R (j + 1 + 1) = c := by unfold Formalism.L2.Col.cOf; omega
  rw [e1, e2]
  show Even (R.k + j * (R.t + 1) + (c + 2) + (R.k + (j + 1 + 1) * (R.t + 1) + c))
  exact ⟨R.k + (j + 1) * (R.t + 1) + c + 1, by ring⟩

end Steps

end GlobalTheory.TwPlaces
