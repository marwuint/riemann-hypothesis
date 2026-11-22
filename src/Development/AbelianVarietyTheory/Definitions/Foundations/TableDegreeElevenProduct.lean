import Mathlib

noncomputable section

namespace GlobalTheory.OT

def lse (x : ℝ) : ℝ := Real.log (Real.exp x + 1)

def xl (x : ℝ) : ℝ := x * Real.log (max 1 x)

def lf (n : ℕ) : ℝ := Real.log (n.factorial : ℝ)

structure Num where
  D : ℕ
  DX : ℕ
  f : ℝ
  r : ℝ
  m : ℝ
  L : ℝ
  j : ℝ
  nW : ℝ
  Np : ℝ
  lrd : ℝ
  LL : ℝ
  lM : ℝ
  lg : ℝ
  lg1 : ℝ
  lp : ℝ
  ld : ℝ
  l4 : ℝ
  l2q : ℝ
  lx : ℝ
  llx : ℝ
  n : ℝ
  w : ℝ
  a : ℝ
  ka : ℝ
  u1 : ℝ
  DF : ℝ
  DFs : ℝ
  RTc : ℝ
  lh : ℝ
  lNc : ℝ
  lpi : ℝ
  lmu : ℝ
  lmu1 : ℝ
  V : ℝ
  hb : ℝ
  logGenusConstant : ℝ
  dS : ℝ
  rS : ℝ
  dP : ℝ
  rP : ℝ
  lNA : ℝ
  Om : ℝ
  nu : ℝ
  lc : ℝ
  leE : ℝ
  ln0 : ℝ
  c1 : ℝ
  sc1 : ℝ
  G1 : ℝ
  CL : ℝ
  lR : ℝ
  rho : ℝ
  dp : ℝ
  gC : ℝ

namespace Num

variable (N : Num)

def Z : ℝ := N.f * N.r * N.L

def b : ℝ := Real.exp N.L

def r2 : ℝ := N.r ^ 2 - 1

def mono (a b c d : ℕ) : ℝ := N.f ^ a * N.r ^ b * N.m ^ c * N.L ^ d

structure H0 : Prop where
  f_ge : 8 ≤ N.f
  r_ge : 9 ≤ N.r
  m_ge : 2 ≤ N.m
  L_ge : 10 ≤ N.L
  fourth_power_le_degree : N.m ^ 4 ≤ N.f
  f_le : N.f ≤ N.r
  zBase_pow_twelve_le : N.Z ^ 12 ≤ N.b
  j_ge : 0 ≤ N.j
  j_le : N.j ≤ N.m
  D_ge : 4 / 9 * N.f * N.r ^ 2 ≤ (N.D : ℝ)
  D_le : (N.D : ℝ) ≤ N.f * N.r ^ 2 / 2
  DX_le : (N.DX : ℝ) ≤ N.f * N.r * N.m
  nW_ge : 40 ≤ N.nW
  nW_le : N.nW ≤ 11 * (N.f * N.r + N.f ^ 2 * N.r ^ 4 * N.L ^ 2 / N.m)
  Np_ge : 0 ≤ N.Np
  Np_le : N.Np ≤ 3 * N.f * N.r ^ 2
  lrd_ge : 1 ≤ N.lrd
  lrd_mem : 0 ≤ N.lrd ∧ N.lrd ≤ 30 * N.L
  LL_mem : 0 ≤ N.LL ∧ N.LL ≤ 30 * N.L
  lM_mem : 0 ≤ N.lM ∧ N.lM ≤ 30 * N.L
  lg_mem : 0 ≤ N.lg ∧ N.lg ≤ 30 * N.L
  genus_log_bound : 0 ≤ N.lg1 ∧ N.lg1 ≤ 30 * N.L
  lp_mem : 0 ≤ N.lp ∧ N.lp ≤ 30 * N.L
  ld_mem : 0 ≤ N.ld ∧ N.ld ≤ 30 * N.L
  fourth_log_bound : 0 ≤ N.l4 ∧ N.l4 ≤ 30 * N.L
  second_log_bound : 0 ≤ N.l2q ∧ N.l2q ≤ 30 * N.L
  lx_mem : 0 ≤ N.lx ∧ N.lx ≤ 30 * N.L
  llx_mem : 0 ≤ N.llx ∧ N.llx ≤ 30 * N.L
  n_mem : 1 ≤ N.n ∧ N.n ≤ N.b ^ 3
  w_mem : 1 ≤ N.w ∧ N.w ≤ N.b ^ 3
  ka_mem : 1 ≤ N.ka ∧ N.ka ≤ N.b ^ 3
  first_unit_bound : 1 ≤ N.u1 ∧ N.u1 ≤ N.b ^ 3
  DFs_mem : 1 ≤ N.DFs ∧ N.DFs ≤ N.b ^ 3
  a_mem : 0 ≤ N.a ∧ N.a ≤ N.b ^ 3
  DF_mem : 0 ≤ N.DF ∧ N.DF ≤ N.b ^ 3
  RTc_mem : 0 ≤ N.RTc ∧ N.RTc ≤ N.b ^ 3
  RTc_le : 2 * N.f ^ 2 * N.m ^ 3 * N.RTc ≤ N.b ^ 2

def hHat : ℝ := N.f * N.lrd + 2 * N.f * Real.log (1 + N.f * N.lrd)

def muHat : ℝ := Real.log 2 + N.hHat + 2 * N.f * (N.r ^ 2 + 1) * N.lM + N.f * (N.r ^ 2 - 1) / 2 * N.lrd

def ncHat : ℝ := max (N.hHat + 2 * N.f * N.lM) (N.muHat + N.f * N.r ^ 2 / 2 * Real.log N.r)

def dsHat : ℝ := 19 * N.f * N.r ^ 2 * N.L + 62 * N.f ^ 2 * N.L

def rsHat : ℝ := 19 * N.f * N.r ^ 2 * N.L + 198 * N.f * N.L

def omHat : ℝ := 2.42 + N.lrd + N.LL

def muLow : ℝ := -(N.f * N.r * Real.log 2) - N.f * N.r ^ 2 / 2 * Real.log N.r

def hat : Num :=
  { N with
    lh := N.hHat
    lNc := N.ncHat
    lpi := N.ncHat
    lmu := N.muHat
    lmu1 := max (N.f * N.r ^ 2 * N.lM + N.f * N.r ^ 2 / 2 * N.lrd + 2 * N.f) N.muHat
    V := 38 * N.f * N.r ^ 2 * N.L
    hb := N.f * N.r ^ 2 * N.lM
    logGenusConstant := 20 * N.f * N.r ^ 2 * N.L
    dS := N.dsHat
    rS := N.rsHat
    dP := N.dsHat + 60 * N.f * N.L + 1.4 * N.r + 1.4
    rP := N.rsHat + 30 * N.L
    lNA := 2 * N.lrd
    Om := N.omHat
    nu := 2 * N.L
    lc := 0
    leE := 2 * N.f * N.lrd
    ln0 := 4 * N.f * N.r ^ 2 * Real.log 5
    c1 := N.r / 2 * N.omHat
    sc1 := N.f * N.r / 2 * N.omHat
    G1 := 1009 * N.Z
    CL := N.Z
    lR := 40 * N.Z
    rho := N.m
    dp := 2 * N.f * N.m
    gC := N.f * N.m * N.r }

structure LetLow : Prop where
  lh : 0 ≤ N.lh
  lNc : 0 ≤ N.lNc
  lpi : 0 ≤ N.lpi
  lmu : N.muLow ≤ N.lmu
  lmu1 : N.muLow ≤ N.lmu1
  V : 0 ≤ N.V
  hb : 0 ≤ N.hb
  logGenusConstant : 0 ≤ N.logGenusConstant
  dS : 0 ≤ N.dS
  rS : 0 ≤ N.rS
  dP : 0 ≤ N.dP
  rP : 0 ≤ N.rP
  lNA : 0 ≤ N.lNA
  Om : 0 ≤ N.Om
  nu : 0 ≤ N.nu
  lc : 0 ≤ N.lc
  leE : 0 ≤ N.leE
  ln0 : 0 ≤ N.ln0
  c1 : 0 ≤ N.c1
  sc1 : 0 ≤ N.sc1
  G1 : 0 ≤ N.G1
  CL : 0 ≤ N.CL
  lR : 0 ≤ N.lR
  rho : 0 ≤ N.rho
  dp : 0 ≤ N.dp
  gC : 0 ≤ N.gC

structure LetLe (N N' : Num) : Prop where
  D : N.D = N'.D
  DX : N.DX = N'.DX
  f : N.f = N'.f
  r : N.r = N'.r
  m : N.m = N'.m
  L : N.L = N'.L
  j : N.j = N'.j
  nW : N.nW = N'.nW
  Np : N.Np = N'.Np
  lrd : N.lrd = N'.lrd
  LL : N.LL = N'.LL
  lM : N.lM = N'.lM
  lg : N.lg = N'.lg
  lg1 : N.lg1 = N'.lg1
  lp : N.lp = N'.lp
  ld : N.ld = N'.ld
  l4 : N.l4 = N'.l4
  l2q : N.l2q = N'.l2q
  lx : N.lx = N'.lx
  llx : N.llx = N'.llx
  n : N.n = N'.n
  w : N.w = N'.w
  a : N.a = N'.a
  ka : N.ka = N'.ka
  u1 : N.u1 = N'.u1
  DF : N.DF = N'.DF
  DFs : N.DFs = N'.DFs
  RTc : N.RTc = N'.RTc
  lh : N.lh ≤ N'.lh
  lNc : N.lNc ≤ N'.lNc
  lpi : N.lpi ≤ N'.lpi
  lmu : N.lmu ≤ N'.lmu
  lmu1 : N.lmu1 ≤ N'.lmu1
  V : N.V ≤ N'.V
  hb : N.hb ≤ N'.hb
  logGenusConstant : N.logGenusConstant ≤ N'.logGenusConstant
  dS : N.dS ≤ N'.dS
  rS : N.rS ≤ N'.rS
  dP : N.dP ≤ N'.dP
  rP : N.rP ≤ N'.rP
  lNA : N.lNA ≤ N'.lNA
  Om : N.Om ≤ N'.Om
  nu : N.nu ≤ N'.nu
  lc : N.lc ≤ N'.lc
  leE : N.leE ≤ N'.leE
  ln0 : N.ln0 ≤ N'.ln0
  c1 : N.c1 ≤ N'.c1
  sc1 : N.sc1 ≤ N'.sc1
  G1 : N.G1 ≤ N'.G1
  CL : N.CL ≤ N'.CL
  lR : N.lR ≤ N'.lR
  rho : N.rho ≤ N'.rho
  dp : N.dp ≤ N'.dp
  gC : N.gC ≤ N'.gC

structure admitted : Prop where
  h0 : N.H0
  low : N.LetLow
  le : LetLe N N.hat

def B : ℝ := N.lM + N.nu + N.lrd + Real.log (N.f * N.r * N.n * N.w * (N.a + 2))

def AO : ℝ := (max (N.dS + N.rS) (N.dP + N.rP))

def o : ℝ := N.dP + N.rP

def Ls : ℝ := N.lg + N.l4

def Lp : ℝ := N.Ls + 2 * N.lp

def G : ℝ := N.G1 + 3 * N.L + 2 * N.AO + 2 * N.f * N.r * N.Lp + 31 * N.f * N.r * N.L

def muM : ℝ := Real.log (2) + N.lh + 2 * N.f * (N.r * N.r + 1) * N.lM + N.f * N.r2 * N.lrd / 2

def P7 : ℝ := 2 + (N.D : ℝ) * Real.log (510 * N.r * N.r) + 4 * N.f * N.f * N.r * N.r * (Real.log (5 * N.f * N.r) + 1.5 * N.lrd + (max (0) (N.lM + Real.log (8 * N.f * N.w) + N.ld / 2))) + N.muM

def MU : ℝ := Real.log (2) + N.f * N.lrd + 2 * N.f * Real.log (1 + N.f * N.lrd) + 2 * N.f * (N.r * N.r + 1) * N.lM + N.f * N.r2 * N.lrd / 2 + N.f * N.r * N.r * Real.log (N.r) / 2

def tableDegreeTwoSeven : ℝ := 2 + lf N.DX + (N.DX : ℝ) * Real.log ((max (4) (16 * N.f * N.r * N.w))) + 4 * N.f * N.f * N.r * N.r * (Real.log (7 * N.f * N.r) + 1.5 * N.lrd + (max (0) (N.lM + Real.log (8 * N.f * N.w) + N.ld / 2 + Real.log (1.77)))) + N.MU + N.f * N.r * N.r * Real.log (1 + 16 * N.w)

def sizeConstantAtParamsWeight : ℝ := (max (90 * (N.f * N.r + 1)) (max (360 * N.f * N.m ^ 3) (max (2 * (3 * N.r + 3 + N.r * Real.log (N.r))) (max (N.nW) (max (1250 * N.r) (max (N.f * N.r * N.r + 6) (11)))))))

def p1 : ℝ := 1 + N.f * N.r * (Real.log (7) + (Real.log (N.f * N.r) + N.lM) / 2)

def p2 : ℝ := 1 + xl (3 * N.dp) / 3

def p3 : ℝ := N.r * (N.p1 + N.p2 + N.dp)

def Ap : ℝ := (max (1) (N.r * N.dp / 4))

def P0 : ℝ := N.p3 + N.Ap * (Real.log (2500 * N.Ap) + 7 * N.lrd + 2 * Real.log ((max (1) (N.dp))))

def PU : ℝ := N.f * N.r * (2 * N.lrd + 2 * Real.log (N.f * N.r) + 3)

def primePairSetFirst : ℝ := 2 * N.PU + Real.log (2 * N.m) + N.lc

def tableDegreeOneSquareM : ℝ := 2 * N.f * N.m * N.m

def cnt : ℝ := N.lM + 2 * N.lrd + N.primePairSetFirst + 1

def Pdeg : ℝ := (1 + N.Om + N.lrd) / 2

def tableDegreeThreeBase : ℝ := 3 * N.lrd + 12.57 * (xl (4 * N.tableDegreeOneSquareM) / 4 + N.tableDegreeOneSquareM * N.cnt + 4) + N.primePairSetFirst + 2 * Real.log (2 * N.f * N.r) + 1 + N.Pdeg

def T7 : ℝ := N.tableDegreeThreeBase + 2 * N.tableDegreeTwoSeven + 10 * (N.D : ℝ) * N.L + (max (N.rS) (N.rP)) / 2

def g0n : ℝ := 1250 * N.r

def n0 : ℝ := N.r + 2 * N.g0n * ((N.DX : ℝ) + 1)

def c0 : ℝ := (N.DX : ℝ) * ((N.DX : ℝ) + 1) / 2

def s1 : ℝ := N.r + N.c0 + 2

def c0p : ℝ := (max (N.s1) (8 * N.f * N.r + 4)) + 7

def ldg : ℝ := N.hb + N.lpi

def g0 : ℝ := N.f * N.r * N.c0p

def tableDegreeFiveTheta : ℝ := N.g0 * (1.5 * N.lM + 2 * Real.log (N.g0) + 6 * N.f * N.lrd + 4)

def Iq : ℝ := N.g0 * N.lM

def Ifr : ℝ := N.g0 * N.lrd + 2 * N.lrd

def c1s : ℝ := N.r * (3 + N.lrd + N.LL) / 2 + 3 * N.r * N.lrd

def Bbad : ℝ := 2 * N.lrd + Real.log (15) + N.lg

def MK : ℝ := N.f * N.c0p * (N.c1s + N.r * N.lrd) / 2 + N.Bbad + N.rP / 2

def rts : ℝ := 0.46 * N.g0

def TH : ℝ := N.tableDegreeFiveTheta + N.Iq + N.Ifr + N.MK + N.rts

def U0 : ℝ := N.TH + 2 * N.ldg

def tableLogDegreeOneTwelve : ℝ := Real.log (10000) + N.leE + N.f * N.lrd + 2 * Real.log (2 * N.f * N.m)

def cubicPeriodConstant : ℝ := 2 * (N.f * N.m * N.r + 8 * N.f ^ 3 * N.m * N.m * N.tableLogDegreeOneTwelve + xl (8 * N.f ^ 3 * N.m * N.m) + 3) + N.ln0

def PPA : ℝ := 3 * (N.D : ℝ) + 3 * N.cubicPeriodConstant

def Xde : ℝ := N.lmu + N.f * N.r * N.r * (1 + Real.log (N.r) / 2) + 3 * (N.D : ℝ) * N.L

def lr0 : ℝ := 2 * N.f * N.r * N.r * Real.log (5)

def Psup : ℝ := N.lr0 / 2 + N.P0 + 2 * N.f * N.r * N.r

def Pt0 : ℝ := N.lr0 / 2 + lse (N.Xde) + N.Psup

def LL0 : ℝ := (N.L + N.lrd) * N.llx + N.LL + N.lx

def Ac : ℝ := 1.5 * N.f * N.r ^ 4 * N.L

def Afr : ℝ := (N.f * N.r * N.r + 3) * N.f * N.r * N.lrd + 3 * N.l2q

def Aun : ℝ := 3 * N.lg + Real.log (15)

def PPe : ℝ := N.Ac + N.Afr + N.Aun

def XW : ℝ := 66 * N.L + N.Np * N.f * N.r * N.lrd

def gG : ℝ := 20 * N.f * N.r * N.r * N.L

def B7 : ℝ := N.P7 + 6 * (N.D : ℝ) * N.L

def Bt : ℝ := N.B7 + N.V

def Gka : ℝ := 3 * N.G

def rtN : ℝ := 0.46 * N.f * N.r * N.Np

def E0 : ℝ := N.f * N.r * (N.c0p + 4 * N.r)

def tableDegreeThreeSecondValue : ℝ := 2 * (1 + N.r) * N.G + N.c1 + N.m * N.lrd

def A0 : ℝ := (2 * N.r * N.G + N.c1 + N.m * N.lrd) * N.f * (N.Np + 1 + 3 * N.r) + 2 * N.G * N.Np + 35 * N.L + 3 * N.o + N.B7 + N.rtN

def PPp : ℝ := 10 * ((N.tableDegreeThreeSecondValue + N.CL * N.LL0) * (1 + N.E0) + N.A0 + N.Gka + 3 * N.tableDegreeThreeBase + N.f * N.r * N.L + N.B7 + N.hb + N.gG)

def al : ℝ := 26 * (N.o + 2 * N.B7 + 4 * N.L + N.tableDegreeThreeSecondValue + N.A0)

def Pa : ℝ := 4.5 * N.f * N.r * N.m + 1.5 * N.f * N.r * N.r + 12 * N.f * N.m * (N.Np + 1)

def Pinf : ℝ := 2 * N.Pt0 + N.PPA + 2 * N.f * N.r * N.c1 + 7 * N.f * N.r * N.r + 2 * N.lNc

def Pfl : ℝ := 3 * N.f * N.r * (N.c1 + 3 * N.m * N.lrd) + 35 * N.L

def xn : ℝ := ((N.D : ℝ) + 1) * (N.o + N.B7 + 1) + 6

def xA : ℝ := 1352 * (N.L + Real.log (1352)) + 4

def QJ : ℝ := 4 * N.tableDegreeThreeSecondValue * N.f * N.r * N.r + 3 * N.A0 + 4 * N.B7 + N.V + N.o + 40 * N.L + N.PPe + N.PPA + 3 * N.Pt0 + 12 * N.f * N.r * (N.c1 + N.m * N.lrd) + 1.5 * N.f * N.r * N.r * N.lrd

def Qc : ℝ := N.PPe + N.XW + 104 * N.L * N.Pa + 3 * N.Pinf

def QH : ℝ := N.xA + 26 * (N.al + N.L) + 2 * N.Bt + N.xn + 1 + N.al + N.Bt / 2 + N.Pfl

def Q6 : ℝ := 1.5 * N.hb + N.U0 + N.o + N.gG + N.V

def PPpp : ℝ := 32 * N.PPp + N.QJ + N.Qc + N.QH + N.Q6

end Num

end GlobalTheory.OT
