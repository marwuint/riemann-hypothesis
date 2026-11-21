import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns

noncomputable section

namespace GlobalTheory.TwU.AtTrue.Cl

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Std

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC}
  {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
  (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
  (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi))

structure IsStd (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop where
  crd : ∀ i hi, A.crd i hi = 1
  iA : HEq A.iA (RingEquiv.refl (AfE B.host.F B.host.E))
  q : HEq A.q ((QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)))
  pt : HEq A.pt (fun i (_ : i ≤ B.R.m) (c : (I.stp u a i).Cl) => ((I.stp u a i).rep c).1.1)
  yb : HEq A.yb (fun c : (I.stp u a (B.R.m - 2 + 1)).Cl => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2)
  ib : ∀ i (hi : i < B.R.m) (c : (I.stp u a i).Cl), HEq (A.ib i hi (chOf i hi.le c)) (Idx.get c.1 hi)
  fb : ∀ i hi β P, A.fb i hi β P = 1
  y0 : ∀ (h : B.R.m - 2 + 1 ≤ B.R.m) (c : (I.stp u a (B.R.m - 2 + 1)).Cl) (P : rowSG (B.primes X) I.sel (I.tup a))
    (β : (charts I l Z u a bad Ch chOf eY K (t.m2 + 1) (cpl_lt t a).le).Ch) (P' : SB t a),
    HEq β (chOf (B.R.m - 2 + 1) h c) → HEq P' P → (cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P).Nonempty →
      ∃ y ∈ cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P, HEq (A.y0 β P') y

end Std

end GlobalTheory.TwU.AtTrue.Cl

end
