import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

instance glvModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lv_rank]; exact R.N_pos i)

instance glvFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (M.lv i v c) :=
  haveI : Finite (M.lv i v c) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

instance glkModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lk_rank]; exact R.N_pos i)

instance glkDualFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (Module.Dual (A.Fv v) (M.lk i v c)) :=
  haveI : Finite (Module.Dual (A.Fv v) (M.lk i v c)) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

end Fm

section Tw

variable (D : D7)

variable {D}

variable (D)

variable {D}

end Tw

end Formalism.MainNotions.product_first_zeroth_parts
