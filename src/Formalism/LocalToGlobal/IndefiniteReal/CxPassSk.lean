import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.IndefiniteReal.LevelAmbTransfer

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) where
  A : FamIn K G Pl0 T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)
  Zsc : DefSub A.fam.amb → IndefScale A.fam.base
  X : CxData A.fam.amb
  gE : Representation ℂ G X.EE

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

abbrev cr : Crd I.A.fam.amb (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A.fam.amb (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A.fam.base.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A.fam.base.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A.fam.base.Tup) :
    Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A.fam.base.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))

structure Hyp (s : ℕ) : Prop where
  ok : I.A.fam.Ok s
  sep : I.A.fam.TypesSep
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A.side I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A.side I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : GUnit I.A I.X I.gE
  gequiv : GEquiv I.A I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

end In

end Formalism.IndefR.CxPass
