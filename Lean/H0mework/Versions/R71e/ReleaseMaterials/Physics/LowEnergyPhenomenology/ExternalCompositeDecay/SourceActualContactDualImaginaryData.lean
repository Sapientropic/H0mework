import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorDual24Exchange
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorContactExchange
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.ActualContactDualImaginary
open MixedSpectatorContactExchange MixedSpectatorDual24Data MixedSpectatorPairedSourceFrame
open scoped Matrix BigOperators

def contactValue (a : Fin 117) : ℂ :=
  ![((-5/72) * (Real.sqrt 30 : ℂ)),
    ((-1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    0,
    ((1/24) * (Real.sqrt 15 : ℂ)),
    0,
    ((-1/24) * (Real.sqrt 15 : ℂ)),
    0,
    ((-5/48) * (Real.sqrt 30 : ℂ)),
    ((-5/144) * (Real.sqrt 30 : ℂ)),
    ((5/144) * (Real.sqrt 30 : ℂ)),
    ((-1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    ((-1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    ((1/16) * (Real.sqrt 15 : ℂ)),
    0,
    0,
    0,
    ((-1/16) * (Real.sqrt 15 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    ((1/48) * (Real.sqrt 15 : ℂ)),
    ((-1/48) * (Real.sqrt 15 : ℂ)),
    ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    ((-3/50) * (Real.sqrt 30 : ℂ)),
    0,
    ((-3/20) * Complex.I),
    0,
    ((3/20) * Complex.I),
    0,
    ((1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ)),
    ((-9/100) * (Real.sqrt 30 : ℂ)),
    ((-3/100) * (Real.sqrt 30 : ℂ)),
    ((3/100) * (Real.sqrt 30 : ℂ)),
    ((-9/40) * Complex.I),
    0,
    0,
    0,
    ((9/40) * Complex.I),
    0,
    0,
    0,
    0,
    0,
    0,
    ((-3/40) * Complex.I),
    ((3/40) * Complex.I),
    ((-3/160) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    ((3/160) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ((-1/80) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    ((1/80) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    ((-1/80) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ((-1/80) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ((-1/80) * (Real.sqrt 30 : ℂ)),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ((-3/50) * (Real.sqrt 30 : ℂ)),
    (1/2),
    (-1/2),
    ((3/50) * (Real.sqrt 30 : ℂ)),
    ((5/36) * (Real.sqrt 30 : ℂ)),
    ((-5/36) * (Real.sqrt 30 : ℂ))] a

def dualNumeratorValue (a : Fin 51) : ℂ :=
  ![(852489/1250000),
    (-28677/250000),
    (-159027/250000),
    ((14773/31250) * Complex.I),
    0,
    0,
    ((7821/12500) * Complex.I),
    (852489/1250000),
    (-159027/250000),
    ((14773/31250) * Complex.I),
    ((7821/12500) * Complex.I),
    ((-7821/12500) * Complex.I),
    ((-14773/31250) * Complex.I),
    ((-7821/12500) * Complex.I),
    ((-14773/31250) * Complex.I),
    (28677/250000),
    (159027/250000),
    (159027/250000),
    (-129/5000),
    (-342/625),
    (183/2500),
    (-2241/5000),
    ((19/5000) * Complex.I),
    ((-1719/5000) * Complex.I),
    ((9/40) * Complex.I),
    ((9/40) * Complex.I),
    (-129/5000),
    (-2241/5000),
    ((-1719/5000) * Complex.I),
    ((19/5000) * Complex.I),
    ((9/40) * Complex.I),
    ((9/40) * Complex.I),
    ((-9/40) * Complex.I),
    ((-9/40) * Complex.I),
    ((-19/5000) * Complex.I),
    ((1719/5000) * Complex.I),
    ((-9/40) * Complex.I),
    ((-9/40) * Complex.I),
    ((1719/5000) * Complex.I),
    ((-19/5000) * Complex.I),
    (-51/250),
    (-51/250),
    (27/100),
    (27/100),
    (-51/250),
    (27/100),
    (9/40),
    ((1/4) * Complex.I),
    ((-1/4) * Complex.I),
    ((1/4) * Complex.I),
    ((-1/4) * Complex.I)] a

def dualDenominatorValue (a : Fin 6) : ℂ :=
  ![(755161/390625),
    (-869/625),
    (-19/100),
    (-19/100),
    (-19/100),
    (-19/100)] a

def dualAxialValue (a b : Fin 24) : ℂ :=
  let entry : ℂ := match a.val, b.val with
    | 0, 0 => dualNumeratorValue 0 / dualDenominatorValue 0
    | 0, 4 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 0, 6 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 0, 10 => dualNumeratorValue 2 / dualDenominatorValue 0
    | 0, 12 => dualNumeratorValue 3 / dualDenominatorValue 0
    | 0, 16 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 0, 18 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 0, 22 => dualNumeratorValue 6 / dualDenominatorValue 0
    | 4, 0 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 4, 4 => dualNumeratorValue 7 / dualDenominatorValue 0
    | 4, 6 => dualNumeratorValue 8 / dualDenominatorValue 0
    | 4, 10 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 4, 12 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 4, 16 => dualNumeratorValue 9 / dualDenominatorValue 0
    | 4, 18 => dualNumeratorValue 10 / dualDenominatorValue 0
    | 4, 22 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 6, 0 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 6, 4 => dualNumeratorValue 8 / dualDenominatorValue 0
    | 6, 6 => dualNumeratorValue 7 / dualDenominatorValue 0
    | 6, 10 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 6, 12 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 6, 16 => dualNumeratorValue 11 / dualDenominatorValue 0
    | 6, 18 => dualNumeratorValue 12 / dualDenominatorValue 0
    | 6, 22 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 10, 0 => dualNumeratorValue 2 / dualDenominatorValue 0
    | 10, 4 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 10, 6 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 10, 10 => dualNumeratorValue 0 / dualDenominatorValue 0
    | 10, 12 => dualNumeratorValue 13 / dualDenominatorValue 0
    | 10, 16 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 10, 18 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 10, 22 => dualNumeratorValue 14 / dualDenominatorValue 0
    | 12, 0 => dualNumeratorValue 14 / dualDenominatorValue 0
    | 12, 4 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 12, 6 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 12, 10 => dualNumeratorValue 6 / dualDenominatorValue 0
    | 12, 12 => dualNumeratorValue 0 / dualDenominatorValue 0
    | 12, 16 => dualNumeratorValue 15 / dualDenominatorValue 0
    | 12, 18 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 12, 22 => dualNumeratorValue 16 / dualDenominatorValue 0
    | 16, 0 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 16, 4 => dualNumeratorValue 12 / dualDenominatorValue 0
    | 16, 6 => dualNumeratorValue 10 / dualDenominatorValue 0
    | 16, 10 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 16, 12 => dualNumeratorValue 15 / dualDenominatorValue 0
    | 16, 16 => dualNumeratorValue 7 / dualDenominatorValue 0
    | 16, 18 => dualNumeratorValue 17 / dualDenominatorValue 0
    | 16, 22 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 18, 0 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 18, 4 => dualNumeratorValue 11 / dualDenominatorValue 0
    | 18, 6 => dualNumeratorValue 9 / dualDenominatorValue 0
    | 18, 10 => dualNumeratorValue 4 / dualDenominatorValue 0
    | 18, 12 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 18, 16 => dualNumeratorValue 17 / dualDenominatorValue 0
    | 18, 18 => dualNumeratorValue 7 / dualDenominatorValue 0
    | 18, 22 => dualNumeratorValue 15 / dualDenominatorValue 0
    | 22, 0 => dualNumeratorValue 13 / dualDenominatorValue 0
    | 22, 4 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 22, 6 => dualNumeratorValue 5 / dualDenominatorValue 0
    | 22, 10 => dualNumeratorValue 3 / dualDenominatorValue 0
    | 22, 12 => dualNumeratorValue 16 / dualDenominatorValue 0
    | 22, 16 => dualNumeratorValue 1 / dualDenominatorValue 0
    | 22, 18 => dualNumeratorValue 15 / dualDenominatorValue 0
    | 22, 22 => dualNumeratorValue 0 / dualDenominatorValue 0
    | 1, 1 => dualNumeratorValue 18 / dualDenominatorValue 1
    | 1, 3 => dualNumeratorValue 19 / dualDenominatorValue 1
    | 1, 7 => dualNumeratorValue 20 / dualDenominatorValue 1
    | 1, 9 => dualNumeratorValue 21 / dualDenominatorValue 1
    | 1, 13 => dualNumeratorValue 22 / dualDenominatorValue 1
    | 1, 15 => dualNumeratorValue 23 / dualDenominatorValue 1
    | 1, 19 => dualNumeratorValue 24 / dualDenominatorValue 1
    | 1, 21 => dualNumeratorValue 25 / dualDenominatorValue 1
    | 3, 1 => dualNumeratorValue 19 / dualDenominatorValue 1
    | 3, 3 => dualNumeratorValue 26 / dualDenominatorValue 1
    | 3, 7 => dualNumeratorValue 27 / dualDenominatorValue 1
    | 3, 9 => dualNumeratorValue 20 / dualDenominatorValue 1
    | 3, 13 => dualNumeratorValue 28 / dualDenominatorValue 1
    | 3, 15 => dualNumeratorValue 29 / dualDenominatorValue 1
    | 3, 19 => dualNumeratorValue 30 / dualDenominatorValue 1
    | 3, 21 => dualNumeratorValue 31 / dualDenominatorValue 1
    | 7, 1 => dualNumeratorValue 20 / dualDenominatorValue 1
    | 7, 3 => dualNumeratorValue 27 / dualDenominatorValue 1
    | 7, 7 => dualNumeratorValue 26 / dualDenominatorValue 1
    | 7, 9 => dualNumeratorValue 19 / dualDenominatorValue 1
    | 7, 13 => dualNumeratorValue 32 / dualDenominatorValue 1
    | 7, 15 => dualNumeratorValue 33 / dualDenominatorValue 1
    | 7, 19 => dualNumeratorValue 34 / dualDenominatorValue 1
    | 7, 21 => dualNumeratorValue 35 / dualDenominatorValue 1
    | 9, 1 => dualNumeratorValue 21 / dualDenominatorValue 1
    | 9, 3 => dualNumeratorValue 20 / dualDenominatorValue 1
    | 9, 7 => dualNumeratorValue 19 / dualDenominatorValue 1
    | 9, 9 => dualNumeratorValue 18 / dualDenominatorValue 1
    | 9, 13 => dualNumeratorValue 36 / dualDenominatorValue 1
    | 9, 15 => dualNumeratorValue 37 / dualDenominatorValue 1
    | 9, 19 => dualNumeratorValue 38 / dualDenominatorValue 1
    | 9, 21 => dualNumeratorValue 39 / dualDenominatorValue 1
    | 13, 1 => dualNumeratorValue 39 / dualDenominatorValue 1
    | 13, 3 => dualNumeratorValue 35 / dualDenominatorValue 1
    | 13, 7 => dualNumeratorValue 31 / dualDenominatorValue 1
    | 13, 9 => dualNumeratorValue 25 / dualDenominatorValue 1
    | 13, 13 => dualNumeratorValue 40 / dualDenominatorValue 1
    | 13, 15 => dualNumeratorValue 41 / dualDenominatorValue 1
    | 13, 19 => dualNumeratorValue 42 / dualDenominatorValue 1
    | 13, 21 => dualNumeratorValue 43 / dualDenominatorValue 1
    | 15, 1 => dualNumeratorValue 38 / dualDenominatorValue 1
    | 15, 3 => dualNumeratorValue 34 / dualDenominatorValue 1
    | 15, 7 => dualNumeratorValue 30 / dualDenominatorValue 1
    | 15, 9 => dualNumeratorValue 24 / dualDenominatorValue 1
    | 15, 13 => dualNumeratorValue 41 / dualDenominatorValue 1
    | 15, 15 => dualNumeratorValue 44 / dualDenominatorValue 1
    | 15, 19 => dualNumeratorValue 45 / dualDenominatorValue 1
    | 15, 21 => dualNumeratorValue 42 / dualDenominatorValue 1
    | 19, 1 => dualNumeratorValue 37 / dualDenominatorValue 1
    | 19, 3 => dualNumeratorValue 33 / dualDenominatorValue 1
    | 19, 7 => dualNumeratorValue 29 / dualDenominatorValue 1
    | 19, 9 => dualNumeratorValue 23 / dualDenominatorValue 1
    | 19, 13 => dualNumeratorValue 42 / dualDenominatorValue 1
    | 19, 15 => dualNumeratorValue 45 / dualDenominatorValue 1
    | 19, 19 => dualNumeratorValue 44 / dualDenominatorValue 1
    | 19, 21 => dualNumeratorValue 41 / dualDenominatorValue 1
    | 21, 1 => dualNumeratorValue 36 / dualDenominatorValue 1
    | 21, 3 => dualNumeratorValue 32 / dualDenominatorValue 1
    | 21, 7 => dualNumeratorValue 28 / dualDenominatorValue 1
    | 21, 9 => dualNumeratorValue 22 / dualDenominatorValue 1
    | 21, 13 => dualNumeratorValue 43 / dualDenominatorValue 1
    | 21, 15 => dualNumeratorValue 42 / dualDenominatorValue 1
    | 21, 19 => dualNumeratorValue 41 / dualDenominatorValue 1
    | 21, 21 => dualNumeratorValue 40 / dualDenominatorValue 1
    | 2, 2 => dualNumeratorValue 46 / dualDenominatorValue 2
    | 2, 14 => dualNumeratorValue 47 / dualDenominatorValue 2
    | 14, 2 => dualNumeratorValue 48 / dualDenominatorValue 2
    | 14, 14 => dualNumeratorValue 46 / dualDenominatorValue 2
    | 5, 5 => dualNumeratorValue 46 / dualDenominatorValue 3
    | 5, 17 => dualNumeratorValue 49 / dualDenominatorValue 3
    | 17, 5 => dualNumeratorValue 50 / dualDenominatorValue 3
    | 17, 17 => dualNumeratorValue 46 / dualDenominatorValue 3
    | 8, 8 => dualNumeratorValue 46 / dualDenominatorValue 4
    | 8, 20 => dualNumeratorValue 50 / dualDenominatorValue 4
    | 20, 8 => dualNumeratorValue 49 / dualDenominatorValue 4
    | 20, 20 => dualNumeratorValue 46 / dualDenominatorValue 4
    | 11, 11 => dualNumeratorValue 46 / dualDenominatorValue 5
    | 11, 23 => dualNumeratorValue 48 / dualDenominatorValue 5
    | 23, 11 => dualNumeratorValue 47 / dualDenominatorValue 5
    | 23, 23 => dualNumeratorValue 46 / dualDenominatorValue 5
    | _, _ => 0
  entry / (SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse : ℂ)

end LowEnergy.ActualContactDualImaginary
