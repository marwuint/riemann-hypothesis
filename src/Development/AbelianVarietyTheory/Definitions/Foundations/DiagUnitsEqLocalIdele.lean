import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem infIdele_snd (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl

theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

end GlobalTheory.Mem.Chr.Model
