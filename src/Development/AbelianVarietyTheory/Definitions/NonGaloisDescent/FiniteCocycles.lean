import Mathlib

noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

def AdicCont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) : Prop :=
  ∀ N : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (f g)

structure Det (n : ℕ) (A E : Type) [CommRing A] [Ring E] [Algebra A E] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : B ⊗[A] E),
    D B' (Algebra.TensorProduct.map f (AlgHom.id A E) x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), D B (b • x) = b ^ n * D B x

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

def chi (y : E) : A[X] := D.D A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)

def lam (i : ℕ) (y : E) : A := (-1) ^ i * (D.chi y).coeff (n - i)

def tr (y : E) : A := D.lam 1 y

def Kills (y : E) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] E), D.D B (1 + h * (1 ⊗ₜ y)) = 1

def pull {E' : Type} [Ring E'] [Algebra A E'] (φ : E' →ₐ[A] E) : Det n A E' where
  D B _ _ := (D.D B).comp (Algebra.TensorProduct.map (AlgHom.id B B) φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (Algebra.TensorProduct.map (AlgHom.id B' B') φ _) = f (D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x))
    rw [← D.nat]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  homog B _ _ b x := by
    change D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ (b • x)) = b ^ n * D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x)
    rw [map_smul, D.homog]

end Det

structure GDet (n : ℕ) (A G : Type) [CommRing A] [Group G] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], MonoidAlgebra B G →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : MonoidAlgebra B G),
    D B' (MonoidAlgebra.mapRingHom G (f : B →+* B') x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : MonoidAlgebra B G), D B (b • x) = b ^ n * D B x

namespace GDet

variable {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)

@[ext] theorem ext {D D' : GDet n A G} (h : ∀ (B : Type) [CommRing B] [Algebra A B] (x), D.D B x = D'.D B x) : D = D' := by
  cases D; cases D'; congr; funext B _ _; exact MonoidHom.ext (h B)

def map {A' : Type} [CommRing A'] (f : A →+* A') : GDet n A' G where
  D B _ _ := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.D B
  nat B B' _ _ _ _ g x :=
    letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
    D.nat B B' { (g : B →+* B') with commutes' := fun a => g.commutes (f a) } x
  homog B _ _ b x := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.homog B b x

def comap {H : Type} [Group H] (φ : H →* G) : GDet n A H where
  D B _ _ := (D.D B).comp (MonoidAlgebra.mapDomainRingHom B φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (MonoidAlgebra.mapDomainRingHom B' φ _) = f (D.D B (MonoidAlgebra.mapDomainRingHom B φ x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp
  homog B _ _ b x := by
    change D.D B (MonoidAlgebra.mapDomainAlgHom B B φ (b • x)) = b ^ n * D.D B (MonoidAlgebra.mapDomainAlgHom B B φ x)
    rw [map_smul, D.homog]

def repAlg {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι A) (B : Type) [CommRing B] [Algebra A B] :
    MonoidAlgebra B G →ₐ[B] Matrix ι ι B :=
  MonoidAlgebra.lift B (Matrix ι ι B) G ((RingHom.mapMatrix (algebraMap A B)).toMonoidHom.comp ρ)

def ofRep (ρ : G →* Matrix (Fin n) (Fin n) A) : GDet n A G where
  D B _ _ := Matrix.detMonoidHom.comp (repAlg ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (repAlg ρ B' _).det = f (repAlg ρ B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => ext i j; simp [repAlg]
  homog B _ _ b x := by
    change (repAlg ρ B (b • x)).det = b ^ n * (repAlg ρ B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]

def chi (y : MonoidAlgebra A G) : A[X] := D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)

def lam (i : ℕ) (y : MonoidAlgebra A G) : A := (-1) ^ i * (D.chi y).coeff (n - i)

def tr (y : MonoidAlgebra A G) : A := D.lam 1 y

def Kills (y : MonoidAlgebra A G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : MonoidAlgebra B G),
    D.D B (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) = 1

def gen {m : ℕ} (y : Fin m → MonoidAlgebra A G) : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
  ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) A) • MonoidAlgebra.mapRingHom G MvPolynomial.C (y j)

def CH : Set (MonoidAlgebra A G) :=
  {z | ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ), ∀ g : G,
    z.coeff g = MvPolynomial.coeff β
      ((Polynomial.aeval (gen y) ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (gen y))).coeff g)}

variable [TopologicalSpace G]

def IsCont (I : Ideal A) : Prop := ∀ i, AdicCont I fun g : G => D.lam i (MonoidAlgebra.single g 1)

end GDet

end GlobalTheory.Pat

noncomputable section

open IsLocalRing

namespace GlobalTheory.Pat

def ContM {X : Type} [TopologicalSpace X] (A : Type) [CommRing A] [IsLocalRing A] (f : X → A) : Prop :=
  AdicCont (maximalIdeal A) f

def PhiFin (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, IsOpen (H : Set G) →
    {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.Finite

def TopGen (B : Type) [CommRing B] [IsLocalRing B] (S : Set B) : Prop :=
  ∀ (N : ℕ) (a : B), ∃ b ∈ Subring.closure S, a - b ∈ maximalIdeal B ^ N

structure PG where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  [tgrp : IsTopologicalGroup G]
  [cpt : CompactSpace G]
  [t2 : T2Space G]
  [td : TotallyDisconnectedSpace G]

attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td

instance : CoeSort PG Type := ⟨PG.G⟩

structure Frame where
  n : ℕ
  n_pos : 0 < n
  l : ℕ
  [hl : Fact l.Prime]
  l_odd : l ≠ 2
  O : Type
  [iO : CommRing O] [iOd : IsDomain O] [iOv : IsDiscreteValuationRing O]
  O_cpl : IsAdicComplete (maximalIdeal O) O
  k_fin : Finite (ResidueField O)
  l_mem : (l : O) ∈ maximalIdeal O
  d0 : ℕ
  Vl : Type
  [iVl : Fintype Vl]
  Gv : Vl → PG
  Gv_phi : ∀ v, PhiFin l (Gv v)
  Mu : ∀ v, Subgroup (Gv v)
  psib : ∀ v, Fin n → (Gv v →* (ResidueField O)ˣ)
  St : Type
  [iSt : Fintype St]
  Iu : St → PG
  Iu_phi : ∀ u, PhiFin l (Iu u)

  Lk : ∀ v, Set (Fin n × Gv v × MvPowerSeries (Fin d0) O)
  Lk_gen : TopGen (MvPowerSeries (Fin d0) O)
    (Set.range (MvPowerSeries.C : O →+* MvPowerSeries (Fin d0) O) ∪ {a | ∃ v i g, (i, g, a) ∈ Lk v})
  Lk_mu : ∀ v i, ∀ g ∈ Mu v, ∃ θ : O, θ - 1 ∈ maximalIdeal O ∧ (i, g, MvPowerSeries.C θ) ∈ Lk v

attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt

namespace Frame
variable (Φ : Frame)

abbrev k : Type := ResidueField Φ.O

abbrev abelian₂ : Type := MvPowerSeries (Fin Φ.d0) Φ.O

abbrev A : Type := PowerSeries Φ.k

abbrev F : Type := FractionRing Φ.A

abbrev Am (m : ℕ) : Type := Φ.A ⧸ Ideal.span {(PowerSeries.X : Φ.A) ^ m}

def jA : Φ.O →+* Φ.A := (PowerSeries.C : Φ.k →+* Φ.A).comp (residue Φ.O)
end Frame

structure PolGp (Φ : Frame) where
  Γ : PG
  sig : Γ →* Γ
  sig_cont : Continuous sig
  sig_sig : ∀ g, sig (sig g) = g
  mu : Γ →* Φ.Oˣ
  mu_cont : ContM Φ.O (fun g => ((mu g : Φ.Oˣ) : Φ.O))
  mu_sig : ∀ g, mu (sig g) = mu g
  iv : ∀ v, Φ.Gv v →* Γ
  iv_cont : ∀ v, Continuous (iv v)
  iu : ∀ u, Φ.Iu u →* Γ
  iu_cont : ∀ u, Continuous (iu u)
  chi : Fin Φ.n → (Γ →* Φ.kˣ)
  chi_open : ∀ i, IsOpen ((chi i).ker : Set Γ)
  chi_inj : Function.Injective chi

  fg : PhiFin Φ.l Γ

structure Mor {Φ : Frame} (G G' : PolGp Φ) where
  p : G.Γ →* G'.Γ
  cont : Continuous p
  surj : Function.Surjective p
  p_sig : ∀ g, p (G.sig g) = G'.sig (p g)
  p_mu : ∀ g, G'.mu (p g) = G.mu g
  p_iv : ∀ v g, p (G.iv v g) = G'.iv v g
  p_iu : ∀ u g, p (G.iu u g) = G'.iu u g
  p_chi : ∀ i g, G'.chi i (p g) = G.chi i g

def Mor.id {Φ : Frame} (G : PolGp Φ) : Mor G G :=
  ⟨MonoidHom.id _, continuous_id, Function.surjective_id, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def Mor.comp {Φ : Frame} {G G' G'' : PolGp Φ} (q : Mor G' G'') (p : Mor G G') : Mor G G'' where
  p := q.p.comp p.p
  cont := q.cont.comp p.cont
  surj := q.surj.comp p.surj
  p_sig g := by rw [MonoidHom.comp_apply, p.p_sig, q.p_sig]; rfl
  p_mu g := (q.p_mu _).trans (p.p_mu g)
  p_iv v g := by rw [MonoidHom.comp_apply, p.p_iv, q.p_iv]
  p_iu u g := by rw [MonoidHom.comp_apply, p.p_iu, q.p_iu]
  p_chi i g := (q.p_chi i _).trans (p.p_chi i g)

abbrev DetG (n : ℕ) (Γ B : Type) [Group Γ] [CommRing B] : Type 1 := GDet n B Γ

abbrev gp {Γ : Type} (B : Type) [Group Γ] [CommRing B] (g : Γ) : MonoidAlgebra B Γ := MonoidAlgebra.single g 1

abbrev sc {B : Type} (Γ : Type) [Group Γ] [CommRing B] (b : B) : MonoidAlgebra B Γ := MonoidAlgebra.single 1 b

def DetCont {n : ℕ} {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing B] [IsLocalRing B]
    (D : DetG n Γ B) : Prop :=
  D.IsCont (maximalIdeal B)

def Red {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) (b : B)
    (x : ResidueField O) : Prop :=
  ∃ o : O, residue O o = x ∧ b - j o ∈ maximalIdeal B

def diagRep {n : ℕ} {Γ K : Type} [Group Γ] [CommRing K] (chi : Fin n → (Γ →* Kˣ)) :
    Γ →* Matrix (Fin n) (Fin n) K where
  toFun g := Matrix.diagonal (fun i => ((chi i g : Kˣ) : K))
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]

def DetLifts {n : ℕ} {Γ O B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B]
    (j : O →+* B) (D : DetG n Γ B) (chi : Fin n → (Γ →* (ResidueField O)ˣ)) : Prop :=
  ∀ κ : ResidueField O →+* ResidueField B, κ.comp (residue O) = (residue B).comp j →
    D.map (residue B) = (GDet.ofRep (diagRep chi)).map κ

structure IsCNL {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) :
    Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  loc : IsLocalHom j
  res : Function.Surjective ((residue B).comp j)

section Elements
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]

def star (j : Φ.O →+* B) (x : MonoidAlgebra B G.Γ) : MonoidAlgebra B G.Γ :=
  x.coeff.sum (fun g a => MonoidAlgebra.single (G.sig g)⁻¹ (a * j ((G.mu g : Φ.Oˣ) : Φ.O)))

def oEl (v : Φ.Vl) (ψ : Fin Φ.n → (Φ.Gv v →* Bˣ)) (g : Fin Φ.n → Φ.Gv v) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i => gp B (G.iv v (g i)) - sc G.Γ ((ψ i (g i) : Bˣ) : B)).prod

def q1El (ph : G.Γ) (u : Fin Φ.n → B) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i => gp B ph - sc G.Γ (u i)).prod

def q2El (ph ta : G.Γ) (u y : Fin Φ.n → B) (i : Fin Φ.n) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i' => if i' = i then 1 else gp B ph - sc G.Γ (u i')).prod *
    (gp B ta - 1 - sc G.Γ (y i))

end Elements

structure Pair {Φ : Frame} (G : PolGp Φ) where
  B : Type
  [iB : CommRing B] [iL : IsLocalRing B]
  lam : Φ.abelian₂ →+* B
  lam_loc : IsLocalHom lam
  cnl : IsCNL (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂))
  D : DetG Φ.n G.Γ B
  psi : ∀ v, Fin Φ.n → (Φ.Gv v →* Bˣ)
  cont : DetCont D
  lift : DetLifts (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) D G.chi
  psi_cont : ∀ v i, ContM B (fun g => ((psi v i g : Bˣ) : B))
  psi_lift : ∀ v i g, Red (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) ((psi v i g : Bˣ) : B)
    ((Φ.psib v i g : Φ.kˣ) : Φ.k)
  link : ∀ v i g a, (i, g, a) ∈ Φ.Lk v → ((psi v i g : Bˣ) : B) = lam a
  relP : ∀ (g : G.Γ) (i : ℕ),
    D.lam i (star G (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) (gp B g)) = D.lam i (gp B g)
  relO : ∀ v (g : Fin Φ.n → Φ.Gv v) (h : G.Γ), D.tr (gp B h * oEl G v (psi v) g) = 0
  relI : ∀ u (g : Φ.Iu u) (h : G.Γ), D.tr (gp B h * (gp B (G.iu u g) - 1)) = 0

attribute [instance] Pair.iB Pair.iL

namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)

def j : Φ.O →+* R.B := R.lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)

def gens : Set R.B :=
  Set.range R.j ∪ {b | ∃ i g, b = R.D.lam i (gp R.B g)} ∪ {b | ∃ v i g, b = ((R.psi v i g : R.Bˣ) : R.B)}

end Pair

namespace Pair
end Pair

end GlobalTheory.Pat

noncomputable section

open IsLocalRing Polynomial

namespace GlobalTheory.Pat.Example

def finPG (G : Type) [Group G] [Finite G] : PG :=
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  { G := G }

instance (G : Type) [Group G] [Finite G] : DiscreteTopology (finPG G) := ⟨rfl⟩

instance (G : Type) [Group G] [Finite G] : Finite (finPG G) := inferInstanceAs (Finite G)

end GlobalTheory.Pat.Example
