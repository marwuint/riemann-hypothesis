import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ContinuousContractNth

noncomputable section

namespace UpperTheory.V.AlgebraTools.Cx

variable {A : Type} [CommRing A]

structure Sel (A : Type) [CommRing A] (ι : Type) : Type 1 where
  G : Cx A
  L : ι → Cx A
  P : ι → Cx A
  res : ∀ i, Hom G (L i)
  inc : ∀ i, Hom (P i) (L i)

namespace Sel

variable {ι : Type} (S : Sel A ι)

structure Map (S T : Sel A ι) where
  g : Hom S.G T.G
  l : ∀ i, Hom (S.L i) (T.L i)
  p : ∀ i, Hom (S.P i) (T.P i)
  res : ∀ i n x, (T.res i).f n (g.f n x) = (l i).f n ((S.res i).f n x)
  inc : ∀ i n x, (T.inc i).f n ((p i).f n x) = (l i).f n ((S.inc i).f n x)

end Sel

def Hom.prodMap {K L K' L' : Cx A} (φ : Hom K K') (ψ : Hom L L') : Hom (prod K L) (prod K' L') :=
  ⟨fun n => (φ.f n).prodMap (ψ.f n), fun n x => Prod.ext (φ.comm n x.1) (ψ.comm n x.2)⟩

section Two

variable (P Q : Type) [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

def twoX : ℕ → Type
  | 0 => P
  | 1 => Q
  | _ + 2 => PUnit

instance twoGrp : ∀ n, AddCommGroup (twoX P Q n)
  | 0 => inferInstanceAs (AddCommGroup P)
  | 1 => inferInstanceAs (AddCommGroup Q)
  | _ + 2 => inferInstanceAs (AddCommGroup PUnit)

instance twoMod : ∀ n, Module A (twoX P Q n)
  | 0 => inferInstanceAs (Module A P)
  | 1 => inferInstanceAs (Module A Q)
  | _ + 2 => inferInstanceAs (Module A PUnit)

variable {P Q}

end Two

def chi (K : Cx A) (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, (-1) ^ n * ((Module.length A (K.H n)).toNat : ℤ)

instance (ι : Type) : Inhabited (Sel A ι) :=
  ⟨⟨default, fun _ => default, fun _ => default, fun _ => Hom.id _, fun _ => Hom.id _⟩⟩

end UpperTheory.V.AlgebraTools.Cx

end
