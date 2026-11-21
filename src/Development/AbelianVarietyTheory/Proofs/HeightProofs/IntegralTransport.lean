import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom basConj basConj_fix omTens pairAut realFac htStd IsFinK)
open scoped TensorProduct

namespace GlobalTheory.LocWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D}

abbrev cG (D : D7) (n : ℕ) : GL (Fin n) (AE D) →* GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (cA D)

theorem matHom_aut (s : ConjIsom V) (g : GA D V) :
    matHom V (s.aut g) = s.PA * cG D _ (matHom V g) * s.PA⁻¹ := rfl

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

variable (K : KfinTied Wl) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) (eG : ∀ V, L.G V ≃* GA D V)
  (eF : L.ChrF →* ((AF D.host.F)ˣ →* Circle))

structure Common : Prop where
  sR : L.sR = true
  meas : ∀ V, Measurable (eG V)
  gF : ∀ V g, g ∈ L.GF V ↔ eG V g ∈ GQ V
  gK : AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ g, g ∈ L.Gk V ↔ IsFinK θ V (K.cpt V) (eG V g)
  mu : ∃ c : HSp D → ℝ, (∀ V, 0 < c V) ∧ ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    Measure.map (eG V) (L.μG V) = ENNReal.ofReal (c V) • μ
  om : ∀ (V W : HSp D) (hV : V.SigOK) (hW : W.SigOK) χ χ', V.rank ≠ W.rank →
    ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ g h,
      L.om V W χ χ' (g, h) = omTens Wl (basConj K V hV) (basConj K W hW) χ χ' (eG V g, eG W h)
  thF : ∀ V W : HSp D, V.rank ≠ W.rank → ∀ Φ, L.thF V W Φ = Wl.evS V W Φ 0
  inj : Function.Injective eF
  mem : ∀ χ, Formalism.L2.Theta.IsHeckeCharF D (eF χ)
  res : ∀ χ a, eF (L.res χ) a = T.eChr χ (idF D a)
  eta : IsEta D (eF L.eta)
  cc : ∀ χ x, T.eChr (L.cc χ) x = T.eChr χ (conjId D x)

end GlobalTheory.LocWCompare

end
