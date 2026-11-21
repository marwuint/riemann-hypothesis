import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K

abbrev complexMatrix3 : Type := Fin 3 → Fin 3 → ℂ

def extC (W : GL (Fin 3) ℂ → ℂ) (m : complexMatrix3) : ℂ :=
  if h : (Matrix.of m).det ≠ 0 then W (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h) else 0

def SmoothC (W : GL (Fin 3) ℂ → ℂ) : Prop := ContDiffOn ℝ (⊤ : ℕ∞) (extC W) {m | (Matrix.of m).det ≠ 0}

def derC (X : Matrix (Fin 3) (Fin 3) ℂ) (W : GL (Fin 3) ℂ → ℂ) (g : GL (Fin 3) ℂ) : ℂ :=
  fderiv ℝ (extC W) (Matrix.of.symm g.val) (Matrix.of.symm (g.val * X))

def derH (i j : Fin 3) (W : GL (Fin 3) ℂ → ℂ) (g : GL (Fin 3) ℂ) : ℂ :=
  (derC (Matrix.single i j 1) W g - Complex.I * derC (Complex.I • Matrix.single i j 1) W g) / 2
def derA (i j : Fin 3) (W : GL (Fin 3) ℂ → ℂ) (g : GL (Fin 3) ℂ) : ℂ :=
  (derC (Matrix.single i j 1) W g + Complex.I * derC (Complex.I • Matrix.single i j 1) W g) / 2

def psiC (x : ℂ) : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (2 * x.re))

def chC (n : ℤ) (s : ℂ) (a : ℂˣ) : ℂ := ((a : ℂ) / ‖(a : ℂ)‖) ^ n * ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s

def gC (n : ℤ) (s : ℂ) : ℂ :=
  (-Complex.I) ^ n.natAbs * Complex.Gammaℂ (1 - s + n.natAbs / 2) / Complex.Gammaℂ (s + n.natAbs / 2)

def complexGL3 (k : ℕ) (n : ℤ) (s : ℂ) : ℂ := gC (n + 2 * (k - 1 : ℕ)) s * gC n s * gC (n - 2 * (k - 1 : ℕ)) s

def mulC : Measure ℂˣ := Measure.comap Units.val (volume.withDensity fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹)

def volC : Measure ℂ := (2 : ENNReal) • volume

def U3 : Set (GL (Fin 3) ℂ) := {k | k.val * k.valᴴ = 1}

structure WhC (k : ℕ) (V : Submodule ℂ (GL (Fin 3) ℂ → ℂ)) (E E' : Fin 3 → Fin 3 → Module.End ℂ V) : Prop where
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x y z g, W (uni x y z * g) = psiC (x + z) * W g
  cen : ∀ W ∈ V, ∀ (a : ℂˣ) g, W (dg a a a * g) = W g
  smooth : ∀ W ∈ V, SmoothC W
  lie : ∀ i j (W : V), (E i j W : GL (Fin 3) ℂ → ℂ) = derH i j W ∧ (E' i j W : GL (Fin 3) ℂ → ℂ) = derA i j W
  gauge : ∀ W ∈ V, ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℂˣ), ∀ o ∈ U3,
    ‖W (dg (a * b) b 1 * o)‖ ≤ C / (‖(a : ℂ)‖ * ‖(b : ℂ)‖) ^ T / ((1 + ‖(a : ℂ)‖) * (1 + ‖(b : ℂ)‖)) ^ N
  int : ∀ W ∈ V, ∀ s : ℂ, 1 / 4 < s.re → Integrable (fun a => W (dg a 1 1) * chC 0 (s - 1) a) mulC
  int' : ∀ W ∈ V, ∀ s : ℂ, s.re < 3 / 4 → Integrable (fun p : ℂˣ × ℂ => W (mm p.1 p.2) * chC 0 s p.1) (mulC.prod volC)
  fe : ∀ W ∈ V, ∀ (n : ℤ) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
    ∫ p : ℂˣ × ℂ, W (mm p.1 p.2) * chC n s p.1 ∂(mulC.prod volC) = complexGL3 k n s * ∫ a, W (dg a 1 1) * chC n (s - 1) a ∂mulC
  cap : ∀ (u : ℂ) (W : V), Formalism.REAL.qdet E (u + 1) W = ((u + (k - 1)) * u * (u - (k - 1))) • W ∧
    Formalism.REAL.qdet E' (u + 1) W = ((u + (k - 1)) * u * (u - (k - 1))) • W
  kfin : ∃ W ∈ V, W ≠ 0 ∧ FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ U3, W' = fun g => W (g * o)})

variable (K : Type) [Field K] [NumberField K]

abbrev PlK : Type := HeightOneSpectrum (𝓞 K)
abbrev Kv (v : PlK K) : Type := v.adicCompletion K
abbrev G3K : Type := AdelicGLn.AdelicGL K 3

instance (v : PlK K) : MeasurableSpace (Kv K v) := borel _
instance (v : PlK K) : BorelSpace (Kv K v) := ⟨rfl⟩

structure DatK where
  k : ℕ
  three : 3 ≤ k
  ν : ∀ v : PlK K, (Kv K v)ˣ →* ℂˣ
  unit : ∀ v, IsUnit1 (ν v)
  bad : Finset (PlK K)
  unr : ∀ v ∉ bad, IsUnramifiedChar (ν v)
  std : ∀ v ∉ bad, IsStd (localAdelicChar K v)

variable {K}

structure AdmK (D : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)) : Prop where
  inf : ∀ (w : InfinitePlace K) (z : w.Completionˣ),
    (c.infiniteComponent w z : ℂ) = chC n (Complex.I * t) (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z)
  bad : D.bad ⊆ S
  unr : ∀ v ∉ S, IsUnramifiedChar (localChar c v)

def eulK (D : DatK K) (c : HeckeCharacter K) (S : Finset (PlK K)) (s : ℂ) : ℂ :=
  ∏' v : {v : PlK K // v ∉ S}, lf3 (D.ν v.1) (localChar c v.1) s

def gamSK (D : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)) (s : ℂ) : ℂ :=
  complexGL3 D.k n (s + Complex.I * t) * ∏ v ∈ S, gam3 (localAdelicChar K v) (D.ν v) (localChar c v) s

def ContK (D : DatK K) (c : HeckeCharacter K) (S : Finset (PlK K)) (Λ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Λ {s | 1 / 4 < s.re} ∧ Ord Λ (1 / 3) ∧ ∀ s : ℂ, 1 < s.re → Λ s = eulK D c S s

def AnK (D : DatK K) : Prop :=
  ∀ c n t S, AdmK D c n t S → ∃ Λ Λ', ContK D c S Λ ∧ ContK D c⁻¹ S Λ' ∧
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → Λ s = gamSK D c n t S s * Λ' (1 - s)

def EAK (X : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace K)) : Module.End ℂ (archSmooth K 3) :=
  uAction (UniversalEnvelopingAlgebra.ι ℝ (⟨X, Submodule.mem_top⟩ : (isExpLieAlgebra K 3).lieSubalgebra))

abbrev diaK (γ : GL (Fin 3) K) : G3K K := AdelicGLn.diagonal K 3 γ

structure WhAK (V : Submodule ℂ (G3K K → ℂ)) : Prop where
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x y z g, W (uni x y z * g) = (adelicChar K (x + z) : ℂ) * W g
  cen : ∀ W ∈ V, ∀ (a : (𝔸[K])ˣ) g, W (dg a a a * g) = W g
  arch : ∀ W ∈ V, IsArchSmooth W
  level : ∀ W ∈ V, ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K 3), ∀ g, ∀ u ∈ U, W (g * finEmb K 3 u) = W g
  lie : ∀ W (hW : W ∈ V) X, ((EAK X ⟨W, arch W hW⟩ : archSmooth K 3) : G3K K → ℂ) ∈ V
  gauge : ∀ W ∈ V, ∃ Ω : Set (FiniteAdeleRing (𝓞 K) K), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[K])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup (G3K K)), ∀ w : InfinitePlace K,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b) ^ T /
        ((1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[K]).2 ∈ Ω ∧ (b : 𝔸[K]).2 ∈ Ω)

def ek (i j : Fin 3) (z : ℂ) : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace K) := Matrix.single i j (0, fun _ => z)

def BCOf (D : Dat) (DK : DatK K) : Prop :=
  ∀ (v : Pl) (w : PlK K), ((pOf v : ℤ) : 𝓞 K) ∈ w.asIdeal → w ∉ DK.bad → v ∉ D.bad →
    ∃ f : ℕ, Ideal.absNorm w.asIdeal = pOf v ^ f ∧ DK.ν w (unifUnit (Kv K w)) = D.ν v (unifUnit (Qv v)) ^ f

def QOut (D : Dat) (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) : Prop :=
  An D ∧ Good D V hV ∧ ∃ U : V →ₗ[ℂ] archSmooth ℚ 3,
    (∀ W : V, IsLeftInvariant (U W : G3 → ℂ) ∧ HasModerateGrowth (U W : G3 → ℂ) ∧ IsCuspidal (U W : G3 → ℂ) ∧
      FourierWhittaker.whittaker (U W : G3 → ℂ) = W) ∧
    (∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : G3 → ℂ) g = (U W : G3 → ℂ) (g * h)) ∧
    ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = EA i j (U W)

variable (K) in

def ThK : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (D : Dat) V (hV : WhA V), QOut D V hV →
    ∃ DK : DatK K, DK.k = D.k ∧ BCOf D DK ∧ AnK DK

end Ad3.K
