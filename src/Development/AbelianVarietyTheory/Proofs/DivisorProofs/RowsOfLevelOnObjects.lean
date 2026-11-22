import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRowsObj

open GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

variable {D : D7}

theorem not_isConjPl (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {PP PP' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : P.Div k PP) (h' : P.Div k' PP') : ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro hc
  obtain ⟨l, -, hl⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  have hle : ∀ {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.E)}, P.Div k Q → l.Mb ≤ Q.asIdeal := fun {k Q} hQ => by
    rw [hl]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    have e : Q.under (𝓞 D.host.K) = P.pb k := hQ
    rw [Ideal.map_le_iff_le_comap, ← e]
    exact le_rfl
  refine PP'.isPrime.ne_top (top_le_iff.1 (l.coprime.ge.trans (sup_le (hle h') ?_)))
  rw [Ideal.map_le_iff_le_comap]
  intro c hc0
  obtain ⟨c', h1, h2⟩ := hc c (hle h hc0)
  have e : (Formalism.L2.Pj.hostOfRecord D).bar c = c' :=
    RingOfIntegers.ext (((Formalism.L2.Pj.hostOfRecord D).bar_eq c).trans h2.symm)
  show (Formalism.L2.Pj.hostOfRecord D).bar c ∈ PP'.asIdeal
  rwa [e]

theorem liftsExist {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) : LiftsExist (Yc D 0) (L.βY 0) (L.dat0 L.triv) := by
  obtain ⟨c, hc⟩ := hL.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  obtain ⟨k', hk'⟩ := (hL.Pg PP').1 (h'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl _ hk hk'

section Mult

variable {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) :
    HasType V β (flag1L L) F := by
  intro κ hκ h
  have hl := GlobalTheory.FlagAction.isLift_one_of_mem hκ
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hl.2.2]; exact P.H.one_mem
  rw [hF κ ⟨hl.1, hl.2.1, hp⟩ h, GlobalTheory.FlagAction.levChi_flag1]
  congr 1
  unfold levChi
  rw [levFn_withP, extendOne_of_mem _ hp, show (⟨_, hp⟩ : P.H) = 1 from Subtype.ext hl.2.2, map_one, one_mul]

theorem mem_mult_withP_iff (hl : LiftsExist V β L) {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (P : LevelP L.Pg L.r ℂ) (U : MMap M) :
    U ∈ Mult θ M (levS V β (withP L P)) (levChi V β (withP L P)) ↔
      U ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) ∧
        ∀ p : P.H, postOn M (actL V β L p.1) U = ((P.chi p : ℂˣ) : ℂ) • U := by
  rw [GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, HasType V β (withP L P) (U v) := fun v κ hκ y => h.lev v κ hκ y
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ y => hasType_flag1 (hT v) κ hκ y, h.equiv, h.cont⟩, fun p => ?_⟩
    ext v y
    exact congrFun (GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (hT v) p (hl _)) y
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ y => ?_, h.equiv, h.cont⟩
    exact IsPLevel.hasType (V := V) (β := β) (L := L) (P := P)
      ⟨fun κ hκ y => h.lev v κ hκ y, fun p => congrArg (fun W : MMap M => W v) (hP p)⟩ κ hκ y

end Mult

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable {R : RealDat D A Ks}

end GlobalTheory.LevelRowsObj

end
