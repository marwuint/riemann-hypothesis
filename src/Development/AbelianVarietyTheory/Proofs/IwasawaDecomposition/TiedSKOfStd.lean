import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.ClassSK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK

