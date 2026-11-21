import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace HeckeValGen

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom

open Classical in

def finiteSingle (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing L), finiteSingle L v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle L v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle L v) x y) }

end HeckeValGen
