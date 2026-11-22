import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm

noncomputable section

namespace GlobalTheory.TwU.AtTrue

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Defs

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)

abbrev Fam (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) : Type 1 :=
  ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
    (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

def ReadsOne (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : Fam I l Z u a i hi bad chOf) : Prop :=
  ∃ k, I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
    ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (k β) = 1

theorem ReadsOne.readsK {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : Fam I l Z u a i hi bad chOf} (h : ReadsOne I l Z u a i hi chOf K) : I.ReadsK l Z u a i hi chOf K :=
  h.imp fun _ hk => hk.1

def charts (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
    (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) :
    ChainCharts (I.rec7 l Z) u a :=
  fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), K i hi⟩

end Defs

def ReadsMove : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Fam I l Z u a i hi bad chOf),
    I.ReadsK l Z u a i hi chOf K → ∃ k : ∀ β, basePts (K β).lev, ReadsOne I l Z u a i hi chOf fun β => moveChart (K β) (k β)

end GlobalTheory.TwU.AtTrue

end
