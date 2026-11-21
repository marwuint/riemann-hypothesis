import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralsAgreeOf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc Model Rep Base Geo Chars RealMaps FinMaps pure PolMatch IsMatched Decay OneConst Coinv IsConst)
open GlobalTheory.WeilM (SB schA)

variable {D : D7}

structure Sit {W W₁ X : HSp D} (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank) : Prop where

  fam : IsInfFam θ

  tri : IsTriple W W₁ X α β

  hν : IsHaarFD W ν 𝓕

  hν₁ : IsHaarFD W₁ ν₁ 𝓕₁

  weilA : IsWeil Bs.ψ true W X β (β / α) ωA

  weilB : IsWeil Bs.ψ false W₁ X α (α / β) ωB

  read : IsReading Bs.ψ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ Bs Γ Xc

  dictA : IsDict (ε := true) e Bs.ψ ωA Γ.M om 1 read.JW read.JX

  dictB : IsDict (ε := false) e Bs.ψ ωB Γ.M' om' (-1) read.JW₁ read.JX

  matched : IsMatched Bs Γ Xc om om' R Rf

  decay : Decay Bs Γ om om'

  const : OneConst Bs Γ Xc om om' R Rf

  coinv : Coinv Bs Γ Xc om om' Rf

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
