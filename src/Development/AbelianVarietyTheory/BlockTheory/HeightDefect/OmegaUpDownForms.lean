import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsSplitting (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) : Prop where
  heckeA : IsHeckeChar D χA
  heckeB : IsHeckeChar D χB
  resA : ResEta D χA A.rank
  resB : ResEta D χB B.rank

theorem IsSplitting.symm {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} (h : IsSplitting A B χA χB) :
    IsSplitting B A χB χA := ⟨h.heckeB, h.heckeA, h.resB, h.resA⟩

abbrev Rep (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) : Type := GA D A × GA D B →* Module.End ℂ (Theta ψ A B)

def kern {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} (om : Rep ψ A B) (f : Theta ψ A B) (g : GA D A) (h : GA D B) : ℂ :=
  thetaFun A B ((om (g, h) f : Theta ψ A B) : WA A B → ℂ)

def IsQuotInt (V : HSp D) (c : ℝ) (φ : GA D V → ℂ) (z : ℂ) : Prop :=
  AllSome (fun m : Measure (GA D V) × Set (GA D V) => IsVolPair D V m.1 m.2) fun m =>
    IntegrableOn φ m.2 m.1 ∧ z = (c : ℂ) * ∫ g in m.2, φ g ∂m.1

structure Core {X : ThetaX D} (T : ThetaTied D X) where

  ψ : AddChar (AF D.host.F) ℂ

  ψ_std : IsStdChar D (-1) ψ

  eUp : ∀ A B : HSp D, A.rank ≤ B.rank → X.Sch A B ≃ₗ[ℂ] Theta ψ A B

  eDn : ∀ A B : HSp D, A.rank < B.rank → X.Sch B A ≃ₗ[ℂ] Theta ψ A B

  om : ∀ (A B : HSp D), A.rank ≤ B.rank → ∀ χA χB : X.Chr, IsSplitting A B (T.eChr χA) (T.eChr χB) → Rep ψ A B

  om_weil : ∀ A B hr χA χB hs, IsWeil ψ (T.eChr χA) (T.eChr χB) (om A B hr χA χB hs)

  thUp : ∀ (A B : HSp D) (hr : A.rank ≤ B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB)),
    A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
      IsQuotInt A (T.petC A) (fun g => kern (om A B hr χA χB hs) (eUp A B hr Φ) g h * T.ev A (φ : X.AF A) g)
        (T.ev B (X.th A B χA χB Φ φ) h)

  thDn : ∀ (A B : HSp D) (hr : A.rank < B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB)),
    B.SigOK → ∀ (Φ : X.Sch B A) (G : X.cusp B) (g : GA D A),
      IsQuotInt B (T.petC B) (fun h => kern (om A B hr.le χA χB hs) (eDn A B hr Φ) g h * T.ev B (G : X.AF B) h)
        (T.ev A (X.th B A χB χA Φ G) g)

namespace Core

variable {X : ThetaX D} {T : ThetaTied D X} (C : Core T)

def toUp (A B : HSp D) (hr : A.rank < B.rank) : X.Sch B A ≃ₗ[ℂ] X.Sch A B :=
  (C.eDn A B hr).trans (C.eUp A B hr.le).symm

def omUp (A B : HSp D) (hr : A.rank ≤ B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB))
    (p : GA D A × GA D B) : Module.End ℂ (X.Sch A B) :=
  (C.eUp A B hr).symm.conj (C.om A B hr χA χB hs p)

def omDn (A B : HSp D) (hr : A.rank < B.rank) (χA χB : X.Chr) (hs : IsSplitting A B (T.eChr χA) (T.eChr χB))
    (p : GA D A × GA D B) : Module.End ℂ (X.Sch B A) :=
  (C.eDn A B hr).symm.conj (C.om A B hr.le χA χB hs p)

end Core

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

end
