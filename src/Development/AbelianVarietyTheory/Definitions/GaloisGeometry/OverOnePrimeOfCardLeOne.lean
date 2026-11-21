import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace GlobalTheory.Formalism.L2.Col

open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.L2.DIV _root_.Formalism.FrobeniusOrbits

export _root_.Formalism.L2.Col (
  Chars Chars.FromHecke Chars.Ok Chars.Tied Dat Dat.Ok FQ_le_EQ Fields Fields.Core Fields.IsCond Fields.Kq Fields.Ok
  Fields.Ok.core Fields.Ok.f_pos Fields.AbelianUnramifiedExtensionConditions Fields.AbelianUnramifiedExtensionConditions.eight_le_f Fields.AbelianUnramifiedExtensionConditions.f_even Fields.AbelianUnramifiedExtensionConditions.four_dvd_f
  Fields.AbelianUnramifiedExtensionConditions.two_le_f Fields.conjO Fields.embBar Fields.embC Fields.f Fields.sig IsEtaT IsMu0 Primes Primes.Ok
  Primes.PiGCong Primes.PiGCong.g_cong Primes.natCast_dvd_intCast Primes.vG Primes.vGs Primes.vT Primes.vTbar QDat
  QDat.HasBase QDat.Off QDat.Ok QDat.TiedTo QDat.empty RowPar RowPar.aMinusRev RowPar.aPlus RowPar.bAt RowPar.dV
  RowPar.eAt RowPar.lamV RowPar.lamVQ RowPar.of RowPar.pOf RowPar.qOf RowPar.sg RowPar.sgHC RowPar.sgQ RowPar.sgTrue
  RowPar.vb Sizes Sizes.T_big Sizes.T_spread Sizes.T_spread_true Sizes.a_pos Sizes.spread_le_N Sizes.two_spread_lt Wts
  Wts.Ok Wts.aTop Wts.bTop Wts.deg Wts.degTrue Wts.lamN Wts.lamTrue Wts.lamV Wts.nuW Wts.sgTrue Wts.sgW divs embQ fin_EQ
  fin_F1Q fin_FQ fin_adjoin fin_sqQ finite_pow_eq fintypePsi hostFields hostTops map_le_of_normal normal_EQ normal_F1Q
  normal_adjoin normal_of_map_le normal_sqQ normal_sup' ofQ shiftW spread_shiftW two_le_N)

instance isCyclotomicExtension_gauss : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

end GlobalTheory.Formalism.L2.Col
