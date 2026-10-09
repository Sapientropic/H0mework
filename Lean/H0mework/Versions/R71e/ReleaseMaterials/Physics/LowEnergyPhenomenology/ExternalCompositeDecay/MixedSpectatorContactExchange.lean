import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorContactVertices

/-! The full polynomial Contact643 table is the paid exact source normal-form
output in matter-vertices/exchange.json. No inverse is recomputed here.
The CAR consumer retains independent source/reader momenta and transfer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorContactExchange
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActiveMatterSectorCharge MixedSpectatorCandidate
open MixedSpectatorContactVertices
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def contactPolynomial (q : Fin 4 → ℂ) (a : Fin 117) : ℂ :=
  ![((-5/72) * (Real.sqrt 30 : ℂ)),
    ((-5/72) * q 0 * (Real.sqrt 30 : ℂ)),
    ((-5/72) * q 1 * (Real.sqrt 30 : ℂ)),
    ((1/24) * (Real.sqrt 15 : ℂ)),
    ((-5/72) * q 2 * (Real.sqrt 30 : ℂ)),
    ((-1/24) * (Real.sqrt 15 : ℂ)),
    ((-5/72) * q 3 * (Real.sqrt 30 : ℂ)),
    ((-5/48) * (Real.sqrt 30 : ℂ)),
    ((-5/144) * (Real.sqrt 30 : ℂ)),
    ((5/144) * (Real.sqrt 30 : ℂ)),
    ((-5/48) * q 0 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 0 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 0 * (Real.sqrt 30 : ℂ)),
    ((1/16) * (Real.sqrt 15 : ℂ)),
    ((-5/48) * q 1 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 1 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 1 * (Real.sqrt 30 : ℂ)),
    ((-1/16) * (Real.sqrt 15 : ℂ)),
    ((-5/48) * q 2 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 2 * (Real.sqrt 30 : ℂ)),
    ((-5/48) * q 3 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 3 * (Real.sqrt 30 : ℂ)),
    ((1/48) * (Real.sqrt 15 : ℂ)),
    ((-1/48) * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 0 * (Real.sqrt 30 : ℂ)),
    ((5/72) * (Real.sqrt 30 : ℂ) * (q 0 ^ 2)),
    ((5/72) * q 0 * q 1 * (Real.sqrt 30 : ℂ)),
    ((-1/24) * q 0 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 0 * q 2 * (Real.sqrt 30 : ℂ)),
    ((1/24) * q 0 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 0 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/48) * q 0 * (Real.sqrt 30 : ℂ)),
    ((5/48) * (Real.sqrt 30 : ℂ) * (q 0 ^ 2)),
    ((5/144) * (Real.sqrt 30 : ℂ) * (q 0 ^ 2)),
    ((-5/144) * (Real.sqrt 30 : ℂ) * (q 0 ^ 2)),
    ((-1/16) * q 0 * (Real.sqrt 15 : ℂ)),
    ((5/48) * q 0 * q 1 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 0 * q 1 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 0 * q 1 * (Real.sqrt 30 : ℂ)),
    ((1/16) * q 0 * (Real.sqrt 15 : ℂ)),
    ((5/48) * q 0 * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 0 * q 2 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 0 * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/48) * q 0 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 0 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 0 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-1/48) * q 0 * (Real.sqrt 15 : ℂ)),
    ((1/48) * q 0 * (Real.sqrt 15 : ℂ)),
    ((-3/160) * (Real.sqrt 30 : ℂ)),
    ((1/16) * q 1 * (Real.sqrt 15 : ℂ)),
    ((1/48) * q 1 * (Real.sqrt 15 : ℂ)),
    ((-1/48) * q 1 * (Real.sqrt 15 : ℂ)),
    ((3/160) * (Real.sqrt 30 : ℂ)),
    ((1/16) * q 2 * (Real.sqrt 15 : ℂ)),
    ((1/48) * q 2 * (Real.sqrt 15 : ℂ)),
    ((-1/48) * q 2 * (Real.sqrt 15 : ℂ)),
    ((1/16) * q 3 * (Real.sqrt 15 : ℂ)),
    ((1/48) * q 3 * (Real.sqrt 15 : ℂ)),
    ((-1/48) * q 3 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 1 * (Real.sqrt 30 : ℂ)),
    (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * (q 1 ^ 2))),
    ((-1/12) * q 1 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 1 * q 2 * (Real.sqrt 30 : ℂ)),
    ((1/80) * (Real.sqrt 30 : ℂ)),
    ((1/24) * q 1 * (Real.sqrt 15 : ℂ)),
    ((-1/24) * q 2 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 1 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-1/24) * q 1 * (Real.sqrt 15 : ℂ)),
    ((-1/24) * q 3 * (Real.sqrt 15 : ℂ)),
    ((1/12) * q 1 * (Real.sqrt 15 : ℂ)),
    ((-1/80) * (Real.sqrt 30 : ℂ)),
    ((1/24) * q 2 * (Real.sqrt 15 : ℂ)),
    ((1/24) * q 3 * (Real.sqrt 15 : ℂ)),
    ((5/48) * q 1 * (Real.sqrt 30 : ℂ)),
    ((-1/16) * q 1 * (Real.sqrt 15 : ℂ)),
    ((5/48) * (Real.sqrt 30 : ℂ) * (q 1 ^ 2)),
    ((5/144) * (Real.sqrt 30 : ℂ) * (q 1 ^ 2)),
    ((-5/144) * (Real.sqrt 30 : ℂ) * (q 1 ^ 2)),
    ((5/48) * q 1 * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 1 * q 2 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 1 * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/48) * q 1 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 1 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 1 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/72) * (Real.sqrt 30 : ℂ) * (q 1 ^ 2)),
    ((-1/16) * q 2 * (Real.sqrt 15 : ℂ)),
    ((-1/16) * q 3 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 2 * (Real.sqrt 30 : ℂ)),
    (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * (q 2 ^ 2))),
    ((1/12) * q 2 * (Real.sqrt 15 : ℂ)),
    ((5/72) * q 2 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-1/12) * q 2 * (Real.sqrt 15 : ℂ)),
    ((5/48) * q 2 * (Real.sqrt 30 : ℂ)),
    ((5/48) * (Real.sqrt 30 : ℂ) * (q 2 ^ 2)),
    ((5/144) * (Real.sqrt 30 : ℂ) * (q 2 ^ 2)),
    ((-5/144) * (Real.sqrt 30 : ℂ) * (q 2 ^ 2)),
    ((5/48) * q 2 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/144) * q 2 * q 3 * (Real.sqrt 30 : ℂ)),
    ((-5/144) * q 2 * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/72) * (Real.sqrt 30 : ℂ) * (q 2 ^ 2)),
    ((5/72) * q 3 * (Real.sqrt 30 : ℂ)),
    (((-1/80) * (Real.sqrt 30 : ℂ)) + ((5/72) * (Real.sqrt 30 : ℂ) * (q 3 ^ 2))),
    ((-1/12) * q 3 * (Real.sqrt 15 : ℂ)),
    ((1/12) * q 3 * (Real.sqrt 15 : ℂ)),
    ((5/48) * q 3 * (Real.sqrt 30 : ℂ)),
    ((5/48) * (Real.sqrt 30 : ℂ) * (q 3 ^ 2)),
    ((5/144) * (Real.sqrt 30 : ℂ) * (q 3 ^ 2)),
    ((-5/144) * (Real.sqrt 30 : ℂ) * (q 3 ^ 2)),
    ((5/72) * (Real.sqrt 30 : ℂ) * (q 3 ^ 2)),
    ((-3/50) * (Real.sqrt 30 : ℂ)),
    (1/2),
    (-1/2),
    ((3/50) * (Real.sqrt 30 : ℂ)),
    ((5/36) * (Real.sqrt 30 : ℂ)),
    ((-5/36) * (Real.sqrt 30 : ℂ))] a

def contactCoefficient (q : Fin 4 → ℂ) (a b : Fin 97) : ℂ :=
  match a.val, b.val with
  | 0, 0 => contactPolynomial q 0
  | 0, 11 => contactPolynomial q 1
  | 0, 23 => contactPolynomial q 2
  | 0, 26 => contactPolynomial q 3
  | 0, 35 => contactPolynomial q 4
  | 0, 37 => contactPolynomial q 5
  | 0, 47 => contactPolynomial q 6
  | 0, 48 => contactPolynomial q 3
  | 1, 1 => contactPolynomial q 0
  | 1, 12 => contactPolynomial q 1
  | 1, 24 => contactPolynomial q 2
  | 1, 25 => contactPolynomial q 5
  | 1, 36 => contactPolynomial q 4
  | 1, 38 => contactPolynomial q 5
  | 1, 47 => contactPolynomial q 5
  | 1, 48 => contactPolynomial q 6
  | 2, 2 => contactPolynomial q 0
  | 2, 13 => contactPolynomial q 1
  | 2, 24 => contactPolynomial q 3
  | 2, 25 => contactPolynomial q 2
  | 2, 35 => contactPolynomial q 3
  | 2, 37 => contactPolynomial q 4
  | 2, 49 => contactPolynomial q 6
  | 2, 50 => contactPolynomial q 5
  | 3, 3 => contactPolynomial q 0
  | 3, 14 => contactPolynomial q 1
  | 3, 23 => contactPolynomial q 5
  | 3, 26 => contactPolynomial q 2
  | 3, 36 => contactPolynomial q 3
  | 3, 38 => contactPolynomial q 4
  | 3, 49 => contactPolynomial q 3
  | 3, 50 => contactPolynomial q 6
  | 4, 4 => contactPolynomial q 7
  | 4, 7 => contactPolynomial q 8
  | 4, 8 => contactPolynomial q 9
  | 4, 15 => contactPolynomial q 10
  | 4, 19 => contactPolynomial q 11
  | 4, 20 => contactPolynomial q 12
  | 4, 21 => contactPolynomial q 13
  | 4, 27 => contactPolynomial q 14
  | 4, 31 => contactPolynomial q 15
  | 4, 32 => contactPolynomial q 16
  | 4, 34 => contactPolynomial q 17
  | 4, 39 => contactPolynomial q 18
  | 4, 43 => contactPolynomial q 19
  | 4, 44 => contactPolynomial q 20
  | 4, 51 => contactPolynomial q 21
  | 4, 55 => contactPolynomial q 22
  | 4, 56 => contactPolynomial q 23
  | 5, 5 => contactPolynomial q 0
  | 5, 17 => contactPolynomial q 1
  | 5, 29 => contactPolynomial q 2
  | 5, 41 => contactPolynomial q 4
  | 5, 53 => contactPolynomial q 6
  | 6, 6 => contactPolynomial q 0
  | 6, 18 => contactPolynomial q 1
  | 6, 30 => contactPolynomial q 2
  | 6, 42 => contactPolynomial q 4
  | 6, 54 => contactPolynomial q 6
  | 7, 4 => contactPolynomial q 8
  | 7, 7 => contactPolynomial q 7
  | 7, 8 => contactPolynomial q 8
  | 7, 15 => contactPolynomial q 11
  | 7, 19 => contactPolynomial q 10
  | 7, 20 => contactPolynomial q 11
  | 7, 21 => contactPolynomial q 24
  | 7, 27 => contactPolynomial q 15
  | 7, 31 => contactPolynomial q 14
  | 7, 32 => contactPolynomial q 15
  | 7, 34 => contactPolynomial q 25
  | 7, 39 => contactPolynomial q 19
  | 7, 43 => contactPolynomial q 18
  | 7, 44 => contactPolynomial q 19
  | 7, 51 => contactPolynomial q 22
  | 7, 55 => contactPolynomial q 21
  | 7, 56 => contactPolynomial q 22
  | 8, 4 => contactPolynomial q 9
  | 8, 7 => contactPolynomial q 8
  | 8, 8 => contactPolynomial q 7
  | 8, 15 => contactPolynomial q 12
  | 8, 19 => contactPolynomial q 11
  | 8, 20 => contactPolynomial q 10
  | 8, 21 => contactPolynomial q 25
  | 8, 27 => contactPolynomial q 16
  | 8, 31 => contactPolynomial q 15
  | 8, 32 => contactPolynomial q 14
  | 8, 34 => contactPolynomial q 24
  | 8, 39 => contactPolynomial q 20
  | 8, 43 => contactPolynomial q 19
  | 8, 44 => contactPolynomial q 18
  | 8, 51 => contactPolynomial q 23
  | 8, 55 => contactPolynomial q 22
  | 8, 56 => contactPolynomial q 21
  | 11, 0 => contactPolynomial q 26
  | 11, 11 => contactPolynomial q 27
  | 11, 23 => contactPolynomial q 28
  | 11, 26 => contactPolynomial q 29
  | 11, 35 => contactPolynomial q 30
  | 11, 37 => contactPolynomial q 31
  | 11, 47 => contactPolynomial q 32
  | 11, 48 => contactPolynomial q 29
  | 12, 1 => contactPolynomial q 26
  | 12, 12 => contactPolynomial q 27
  | 12, 24 => contactPolynomial q 28
  | 12, 25 => contactPolynomial q 31
  | 12, 36 => contactPolynomial q 30
  | 12, 38 => contactPolynomial q 31
  | 12, 47 => contactPolynomial q 31
  | 12, 48 => contactPolynomial q 32
  | 13, 2 => contactPolynomial q 26
  | 13, 13 => contactPolynomial q 27
  | 13, 24 => contactPolynomial q 29
  | 13, 25 => contactPolynomial q 28
  | 13, 35 => contactPolynomial q 29
  | 13, 37 => contactPolynomial q 30
  | 13, 49 => contactPolynomial q 32
  | 13, 50 => contactPolynomial q 31
  | 14, 3 => contactPolynomial q 26
  | 14, 14 => contactPolynomial q 27
  | 14, 23 => contactPolynomial q 31
  | 14, 26 => contactPolynomial q 28
  | 14, 36 => contactPolynomial q 29
  | 14, 38 => contactPolynomial q 30
  | 14, 49 => contactPolynomial q 29
  | 14, 50 => contactPolynomial q 32
  | 15, 4 => contactPolynomial q 33
  | 15, 7 => contactPolynomial q 12
  | 15, 8 => contactPolynomial q 11
  | 15, 15 => contactPolynomial q 34
  | 15, 19 => contactPolynomial q 35
  | 15, 20 => contactPolynomial q 36
  | 15, 21 => contactPolynomial q 37
  | 15, 27 => contactPolynomial q 38
  | 15, 31 => contactPolynomial q 39
  | 15, 32 => contactPolynomial q 40
  | 15, 34 => contactPolynomial q 41
  | 15, 39 => contactPolynomial q 42
  | 15, 43 => contactPolynomial q 43
  | 15, 44 => contactPolynomial q 44
  | 15, 51 => contactPolynomial q 45
  | 15, 55 => contactPolynomial q 46
  | 15, 56 => contactPolynomial q 47
  | 17, 5 => contactPolynomial q 26
  | 17, 17 => contactPolynomial q 27
  | 17, 29 => contactPolynomial q 28
  | 17, 41 => contactPolynomial q 30
  | 17, 53 => contactPolynomial q 32
  | 18, 6 => contactPolynomial q 26
  | 18, 18 => contactPolynomial q 27
  | 18, 30 => contactPolynomial q 28
  | 18, 42 => contactPolynomial q 30
  | 18, 54 => contactPolynomial q 32
  | 19, 4 => contactPolynomial q 12
  | 19, 7 => contactPolynomial q 33
  | 19, 8 => contactPolynomial q 12
  | 19, 15 => contactPolynomial q 35
  | 19, 19 => contactPolynomial q 34
  | 19, 20 => contactPolynomial q 35
  | 19, 21 => contactPolynomial q 48
  | 19, 27 => contactPolynomial q 39
  | 19, 31 => contactPolynomial q 38
  | 19, 32 => contactPolynomial q 39
  | 19, 34 => contactPolynomial q 49
  | 19, 39 => contactPolynomial q 43
  | 19, 43 => contactPolynomial q 42
  | 19, 44 => contactPolynomial q 43
  | 19, 51 => contactPolynomial q 46
  | 19, 55 => contactPolynomial q 45
  | 19, 56 => contactPolynomial q 46
  | 20, 4 => contactPolynomial q 11
  | 20, 7 => contactPolynomial q 12
  | 20, 8 => contactPolynomial q 33
  | 20, 15 => contactPolynomial q 36
  | 20, 19 => contactPolynomial q 35
  | 20, 20 => contactPolynomial q 34
  | 20, 21 => contactPolynomial q 49
  | 20, 27 => contactPolynomial q 40
  | 20, 31 => contactPolynomial q 39
  | 20, 32 => contactPolynomial q 38
  | 20, 34 => contactPolynomial q 48
  | 20, 39 => contactPolynomial q 44
  | 20, 43 => contactPolynomial q 43
  | 20, 44 => contactPolynomial q 42
  | 20, 51 => contactPolynomial q 47
  | 20, 55 => contactPolynomial q 46
  | 20, 56 => contactPolynomial q 45
  | 21, 4 => contactPolynomial q 13
  | 21, 7 => contactPolynomial q 24
  | 21, 8 => contactPolynomial q 25
  | 21, 15 => contactPolynomial q 41
  | 21, 19 => contactPolynomial q 49
  | 21, 20 => contactPolynomial q 48
  | 21, 21 => contactPolynomial q 50
  | 21, 27 => contactPolynomial q 51
  | 21, 31 => contactPolynomial q 52
  | 21, 32 => contactPolynomial q 53
  | 21, 34 => contactPolynomial q 54
  | 21, 39 => contactPolynomial q 55
  | 21, 43 => contactPolynomial q 56
  | 21, 44 => contactPolynomial q 57
  | 21, 51 => contactPolynomial q 58
  | 21, 55 => contactPolynomial q 59
  | 21, 56 => contactPolynomial q 60
  | 23, 0 => contactPolynomial q 61
  | 23, 3 => contactPolynomial q 5
  | 23, 11 => contactPolynomial q 28
  | 23, 14 => contactPolynomial q 29
  | 23, 23 => contactPolynomial q 62
  | 23, 26 => contactPolynomial q 63
  | 23, 35 => contactPolynomial q 64
  | 23, 36 => contactPolynomial q 65
  | 23, 37 => contactPolynomial q 66
  | 23, 38 => contactPolynomial q 67
  | 23, 47 => contactPolynomial q 68
  | 23, 48 => contactPolynomial q 69
  | 23, 49 => contactPolynomial q 65
  | 23, 50 => contactPolynomial q 70
  | 24, 1 => contactPolynomial q 61
  | 24, 2 => contactPolynomial q 3
  | 24, 12 => contactPolynomial q 28
  | 24, 13 => contactPolynomial q 31
  | 24, 24 => contactPolynomial q 62
  | 24, 25 => contactPolynomial q 71
  | 24, 35 => contactPolynomial q 72
  | 24, 36 => contactPolynomial q 64
  | 24, 37 => contactPolynomial q 73
  | 24, 38 => contactPolynomial q 66
  | 24, 47 => contactPolynomial q 66
  | 24, 48 => contactPolynomial q 68
  | 24, 49 => contactPolynomial q 74
  | 24, 50 => contactPolynomial q 65
  | 25, 1 => contactPolynomial q 5
  | 25, 2 => contactPolynomial q 61
  | 25, 12 => contactPolynomial q 29
  | 25, 13 => contactPolynomial q 28
  | 25, 24 => contactPolynomial q 63
  | 25, 25 => contactPolynomial q 62
  | 25, 35 => contactPolynomial q 69
  | 25, 36 => contactPolynomial q 67
  | 25, 37 => contactPolynomial q 64
  | 25, 38 => contactPolynomial q 72
  | 25, 47 => contactPolynomial q 72
  | 25, 48 => contactPolynomial q 70
  | 25, 49 => contactPolynomial q 68
  | 25, 50 => contactPolynomial q 66
  | 26, 0 => contactPolynomial q 3
  | 26, 3 => contactPolynomial q 61
  | 26, 11 => contactPolynomial q 31
  | 26, 14 => contactPolynomial q 28
  | 26, 23 => contactPolynomial q 71
  | 26, 26 => contactPolynomial q 62
  | 26, 35 => contactPolynomial q 73
  | 26, 36 => contactPolynomial q 69
  | 26, 37 => contactPolynomial q 65
  | 26, 38 => contactPolynomial q 64
  | 26, 47 => contactPolynomial q 74
  | 26, 48 => contactPolynomial q 72
  | 26, 49 => contactPolynomial q 69
  | 26, 50 => contactPolynomial q 68
  | 27, 4 => contactPolynomial q 75
  | 27, 7 => contactPolynomial q 16
  | 27, 8 => contactPolynomial q 15
  | 27, 15 => contactPolynomial q 38
  | 27, 19 => contactPolynomial q 39
  | 27, 20 => contactPolynomial q 40
  | 27, 21 => contactPolynomial q 76
  | 27, 27 => contactPolynomial q 77
  | 27, 31 => contactPolynomial q 78
  | 27, 32 => contactPolynomial q 79
  | 27, 34 => contactPolynomial q 51
  | 27, 39 => contactPolynomial q 80
  | 27, 43 => contactPolynomial q 81
  | 27, 44 => contactPolynomial q 82
  | 27, 51 => contactPolynomial q 83
  | 27, 55 => contactPolynomial q 84
  | 27, 56 => contactPolynomial q 85
  | 29, 5 => contactPolynomial q 61
  | 29, 17 => contactPolynomial q 28
  | 29, 29 => contactPolynomial q 86
  | 29, 41 => contactPolynomial q 64
  | 29, 53 => contactPolynomial q 68
  | 30, 6 => contactPolynomial q 61
  | 30, 18 => contactPolynomial q 28
  | 30, 30 => contactPolynomial q 86
  | 30, 42 => contactPolynomial q 64
  | 30, 54 => contactPolynomial q 68
  | 31, 4 => contactPolynomial q 16
  | 31, 7 => contactPolynomial q 75
  | 31, 8 => contactPolynomial q 16
  | 31, 15 => contactPolynomial q 39
  | 31, 19 => contactPolynomial q 38
  | 31, 20 => contactPolynomial q 39
  | 31, 21 => contactPolynomial q 53
  | 31, 27 => contactPolynomial q 78
  | 31, 31 => contactPolynomial q 77
  | 31, 32 => contactPolynomial q 78
  | 31, 34 => contactPolynomial q 52
  | 31, 39 => contactPolynomial q 81
  | 31, 43 => contactPolynomial q 80
  | 31, 44 => contactPolynomial q 81
  | 31, 51 => contactPolynomial q 84
  | 31, 55 => contactPolynomial q 83
  | 31, 56 => contactPolynomial q 84
  | 32, 4 => contactPolynomial q 15
  | 32, 7 => contactPolynomial q 16
  | 32, 8 => contactPolynomial q 75
  | 32, 15 => contactPolynomial q 40
  | 32, 19 => contactPolynomial q 39
  | 32, 20 => contactPolynomial q 38
  | 32, 21 => contactPolynomial q 52
  | 32, 27 => contactPolynomial q 79
  | 32, 31 => contactPolynomial q 78
  | 32, 32 => contactPolynomial q 77
  | 32, 34 => contactPolynomial q 53
  | 32, 39 => contactPolynomial q 82
  | 32, 43 => contactPolynomial q 81
  | 32, 44 => contactPolynomial q 80
  | 32, 51 => contactPolynomial q 85
  | 32, 55 => contactPolynomial q 84
  | 32, 56 => contactPolynomial q 83
  | 34, 4 => contactPolynomial q 17
  | 34, 7 => contactPolynomial q 25
  | 34, 8 => contactPolynomial q 24
  | 34, 15 => contactPolynomial q 37
  | 34, 19 => contactPolynomial q 48
  | 34, 20 => contactPolynomial q 49
  | 34, 21 => contactPolynomial q 54
  | 34, 27 => contactPolynomial q 76
  | 34, 31 => contactPolynomial q 53
  | 34, 32 => contactPolynomial q 52
  | 34, 34 => contactPolynomial q 50
  | 34, 39 => contactPolynomial q 87
  | 34, 43 => contactPolynomial q 57
  | 34, 44 => contactPolynomial q 56
  | 34, 51 => contactPolynomial q 88
  | 34, 55 => contactPolynomial q 60
  | 34, 56 => contactPolynomial q 59
  | 35, 0 => contactPolynomial q 89
  | 35, 2 => contactPolynomial q 3
  | 35, 11 => contactPolynomial q 30
  | 35, 13 => contactPolynomial q 31
  | 35, 23 => contactPolynomial q 64
  | 35, 24 => contactPolynomial q 72
  | 35, 25 => contactPolynomial q 66
  | 35, 26 => contactPolynomial q 67
  | 35, 35 => contactPolynomial q 90
  | 35, 37 => contactPolynomial q 91
  | 35, 47 => contactPolynomial q 92
  | 35, 48 => contactPolynomial q 67
  | 35, 49 => contactPolynomial q 74
  | 35, 50 => contactPolynomial q 65
  | 36, 1 => contactPolynomial q 89
  | 36, 3 => contactPolynomial q 3
  | 36, 12 => contactPolynomial q 30
  | 36, 14 => contactPolynomial q 31
  | 36, 23 => contactPolynomial q 65
  | 36, 24 => contactPolynomial q 64
  | 36, 25 => contactPolynomial q 73
  | 36, 26 => contactPolynomial q 66
  | 36, 36 => contactPolynomial q 90
  | 36, 38 => contactPolynomial q 91
  | 36, 47 => contactPolynomial q 73
  | 36, 48 => contactPolynomial q 92
  | 36, 49 => contactPolynomial q 72
  | 36, 50 => contactPolynomial q 74
  | 37, 0 => contactPolynomial q 5
  | 37, 2 => contactPolynomial q 89
  | 37, 11 => contactPolynomial q 29
  | 37, 13 => contactPolynomial q 30
  | 37, 23 => contactPolynomial q 69
  | 37, 24 => contactPolynomial q 67
  | 37, 25 => contactPolynomial q 64
  | 37, 26 => contactPolynomial q 65
  | 37, 35 => contactPolynomial q 93
  | 37, 37 => contactPolynomial q 90
  | 37, 47 => contactPolynomial q 70
  | 37, 48 => contactPolynomial q 65
  | 37, 49 => contactPolynomial q 92
  | 37, 50 => contactPolynomial q 73
  | 38, 1 => contactPolynomial q 5
  | 38, 3 => contactPolynomial q 89
  | 38, 12 => contactPolynomial q 29
  | 38, 14 => contactPolynomial q 30
  | 38, 23 => contactPolynomial q 73
  | 38, 24 => contactPolynomial q 69
  | 38, 25 => contactPolynomial q 72
  | 38, 26 => contactPolynomial q 64
  | 38, 36 => contactPolynomial q 93
  | 38, 38 => contactPolynomial q 90
  | 38, 47 => contactPolynomial q 72
  | 38, 48 => contactPolynomial q 70
  | 38, 49 => contactPolynomial q 67
  | 38, 50 => contactPolynomial q 92
  | 39, 4 => contactPolynomial q 94
  | 39, 7 => contactPolynomial q 20
  | 39, 8 => contactPolynomial q 19
  | 39, 15 => contactPolynomial q 42
  | 39, 19 => contactPolynomial q 43
  | 39, 20 => contactPolynomial q 44
  | 39, 21 => contactPolynomial q 87
  | 39, 27 => contactPolynomial q 80
  | 39, 31 => contactPolynomial q 81
  | 39, 32 => contactPolynomial q 82
  | 39, 34 => contactPolynomial q 55
  | 39, 39 => contactPolynomial q 95
  | 39, 43 => contactPolynomial q 96
  | 39, 44 => contactPolynomial q 97
  | 39, 51 => contactPolynomial q 98
  | 39, 55 => contactPolynomial q 99
  | 39, 56 => contactPolynomial q 100
  | 41, 5 => contactPolynomial q 89
  | 41, 17 => contactPolynomial q 30
  | 41, 29 => contactPolynomial q 64
  | 41, 41 => contactPolynomial q 101
  | 41, 53 => contactPolynomial q 92
  | 42, 6 => contactPolynomial q 89
  | 42, 18 => contactPolynomial q 30
  | 42, 30 => contactPolynomial q 64
  | 42, 42 => contactPolynomial q 101
  | 42, 54 => contactPolynomial q 92
  | 43, 4 => contactPolynomial q 20
  | 43, 7 => contactPolynomial q 94
  | 43, 8 => contactPolynomial q 20
  | 43, 15 => contactPolynomial q 43
  | 43, 19 => contactPolynomial q 42
  | 43, 20 => contactPolynomial q 43
  | 43, 21 => contactPolynomial q 57
  | 43, 27 => contactPolynomial q 81
  | 43, 31 => contactPolynomial q 80
  | 43, 32 => contactPolynomial q 81
  | 43, 34 => contactPolynomial q 56
  | 43, 39 => contactPolynomial q 96
  | 43, 43 => contactPolynomial q 95
  | 43, 44 => contactPolynomial q 96
  | 43, 51 => contactPolynomial q 99
  | 43, 55 => contactPolynomial q 98
  | 43, 56 => contactPolynomial q 99
  | 44, 4 => contactPolynomial q 19
  | 44, 7 => contactPolynomial q 20
  | 44, 8 => contactPolynomial q 94
  | 44, 15 => contactPolynomial q 44
  | 44, 19 => contactPolynomial q 43
  | 44, 20 => contactPolynomial q 42
  | 44, 21 => contactPolynomial q 56
  | 44, 27 => contactPolynomial q 82
  | 44, 31 => contactPolynomial q 81
  | 44, 32 => contactPolynomial q 80
  | 44, 34 => contactPolynomial q 57
  | 44, 39 => contactPolynomial q 97
  | 44, 43 => contactPolynomial q 96
  | 44, 44 => contactPolynomial q 95
  | 44, 51 => contactPolynomial q 100
  | 44, 55 => contactPolynomial q 99
  | 44, 56 => contactPolynomial q 98
  | 47, 0 => contactPolynomial q 102
  | 47, 1 => contactPolynomial q 5
  | 47, 11 => contactPolynomial q 32
  | 47, 12 => contactPolynomial q 29
  | 47, 23 => contactPolynomial q 68
  | 47, 24 => contactPolynomial q 69
  | 47, 25 => contactPolynomial q 72
  | 47, 26 => contactPolynomial q 70
  | 47, 35 => contactPolynomial q 92
  | 47, 36 => contactPolynomial q 67
  | 47, 37 => contactPolynomial q 74
  | 47, 38 => contactPolynomial q 72
  | 47, 47 => contactPolynomial q 103
  | 47, 48 => contactPolynomial q 104
  | 48, 0 => contactPolynomial q 3
  | 48, 1 => contactPolynomial q 102
  | 48, 11 => contactPolynomial q 31
  | 48, 12 => contactPolynomial q 32
  | 48, 23 => contactPolynomial q 66
  | 48, 24 => contactPolynomial q 68
  | 48, 25 => contactPolynomial q 74
  | 48, 26 => contactPolynomial q 72
  | 48, 35 => contactPolynomial q 73
  | 48, 36 => contactPolynomial q 92
  | 48, 37 => contactPolynomial q 65
  | 48, 38 => contactPolynomial q 74
  | 48, 47 => contactPolynomial q 105
  | 48, 48 => contactPolynomial q 103
  | 49, 2 => contactPolynomial q 102
  | 49, 3 => contactPolynomial q 3
  | 49, 13 => contactPolynomial q 32
  | 49, 14 => contactPolynomial q 31
  | 49, 23 => contactPolynomial q 65
  | 49, 24 => contactPolynomial q 70
  | 49, 25 => contactPolynomial q 68
  | 49, 26 => contactPolynomial q 66
  | 49, 35 => contactPolynomial q 70
  | 49, 36 => contactPolynomial q 72
  | 49, 37 => contactPolynomial q 92
  | 49, 38 => contactPolynomial q 73
  | 49, 49 => contactPolynomial q 103
  | 49, 50 => contactPolynomial q 105
  | 50, 2 => contactPolynomial q 5
  | 50, 3 => contactPolynomial q 102
  | 50, 13 => contactPolynomial q 29
  | 50, 14 => contactPolynomial q 32
  | 50, 23 => contactPolynomial q 74
  | 50, 24 => contactPolynomial q 65
  | 50, 25 => contactPolynomial q 69
  | 50, 26 => contactPolynomial q 68
  | 50, 35 => contactPolynomial q 65
  | 50, 36 => contactPolynomial q 70
  | 50, 37 => contactPolynomial q 67
  | 50, 38 => contactPolynomial q 92
  | 50, 49 => contactPolynomial q 104
  | 50, 50 => contactPolynomial q 103
  | 51, 4 => contactPolynomial q 106
  | 51, 7 => contactPolynomial q 23
  | 51, 8 => contactPolynomial q 22
  | 51, 15 => contactPolynomial q 45
  | 51, 19 => contactPolynomial q 46
  | 51, 20 => contactPolynomial q 47
  | 51, 21 => contactPolynomial q 88
  | 51, 27 => contactPolynomial q 83
  | 51, 31 => contactPolynomial q 84
  | 51, 32 => contactPolynomial q 85
  | 51, 34 => contactPolynomial q 58
  | 51, 39 => contactPolynomial q 98
  | 51, 43 => contactPolynomial q 99
  | 51, 44 => contactPolynomial q 100
  | 51, 51 => contactPolynomial q 107
  | 51, 55 => contactPolynomial q 108
  | 51, 56 => contactPolynomial q 109
  | 53, 5 => contactPolynomial q 102
  | 53, 17 => contactPolynomial q 32
  | 53, 29 => contactPolynomial q 68
  | 53, 41 => contactPolynomial q 92
  | 53, 53 => contactPolynomial q 110
  | 54, 6 => contactPolynomial q 102
  | 54, 18 => contactPolynomial q 32
  | 54, 30 => contactPolynomial q 68
  | 54, 42 => contactPolynomial q 92
  | 54, 54 => contactPolynomial q 110
  | 55, 4 => contactPolynomial q 23
  | 55, 7 => contactPolynomial q 106
  | 55, 8 => contactPolynomial q 23
  | 55, 15 => contactPolynomial q 46
  | 55, 19 => contactPolynomial q 45
  | 55, 20 => contactPolynomial q 46
  | 55, 21 => contactPolynomial q 60
  | 55, 27 => contactPolynomial q 84
  | 55, 31 => contactPolynomial q 83
  | 55, 32 => contactPolynomial q 84
  | 55, 34 => contactPolynomial q 59
  | 55, 39 => contactPolynomial q 99
  | 55, 43 => contactPolynomial q 98
  | 55, 44 => contactPolynomial q 99
  | 55, 51 => contactPolynomial q 108
  | 55, 55 => contactPolynomial q 107
  | 55, 56 => contactPolynomial q 108
  | 56, 4 => contactPolynomial q 22
  | 56, 7 => contactPolynomial q 23
  | 56, 8 => contactPolynomial q 106
  | 56, 15 => contactPolynomial q 47
  | 56, 19 => contactPolynomial q 46
  | 56, 20 => contactPolynomial q 45
  | 56, 21 => contactPolynomial q 59
  | 56, 27 => contactPolynomial q 85
  | 56, 31 => contactPolynomial q 84
  | 56, 32 => contactPolynomial q 83
  | 56, 34 => contactPolynomial q 60
  | 56, 39 => contactPolynomial q 100
  | 56, 43 => contactPolynomial q 99
  | 56, 44 => contactPolynomial q 98
  | 56, 51 => contactPolynomial q 109
  | 56, 55 => contactPolynomial q 108
  | 56, 56 => contactPolynomial q 107
  | 73, 73 => contactPolynomial q 111
  | 73, 90 => contactPolynomial q 112
  | 73, 95 => contactPolynomial q 113
  | 74, 74 => contactPolynomial q 111
  | 74, 84 => contactPolynomial q 113
  | 74, 94 => contactPolynomial q 112
  | 75, 75 => contactPolynomial q 111
  | 75, 83 => contactPolynomial q 112
  | 75, 88 => contactPolynomial q 113
  | 76, 76 => contactPolynomial q 114
  | 76, 87 => contactPolynomial q 112
  | 76, 92 => contactPolynomial q 113
  | 77, 77 => contactPolynomial q 114
  | 77, 81 => contactPolynomial q 113
  | 77, 91 => contactPolynomial q 112
  | 78, 78 => contactPolynomial q 114
  | 78, 80 => contactPolynomial q 112
  | 78, 85 => contactPolynomial q 113
  | 79, 79 => contactPolynomial q 115
  | 79, 86 => contactPolynomial q 116
  | 79, 93 => contactPolynomial q 116
  | 80, 78 => contactPolynomial q 112
  | 80, 80 => contactPolynomial q 115
  | 80, 85 => contactPolynomial q 115
  | 81, 77 => contactPolynomial q 113
  | 81, 81 => contactPolynomial q 115
  | 81, 91 => contactPolynomial q 115
  | 82, 82 => contactPolynomial q 116
  | 82, 89 => contactPolynomial q 115
  | 82, 96 => contactPolynomial q 115
  | 83, 75 => contactPolynomial q 112
  | 83, 83 => contactPolynomial q 116
  | 83, 88 => contactPolynomial q 116
  | 84, 74 => contactPolynomial q 113
  | 84, 84 => contactPolynomial q 116
  | 84, 94 => contactPolynomial q 116
  | 85, 78 => contactPolynomial q 113
  | 85, 80 => contactPolynomial q 115
  | 85, 85 => contactPolynomial q 115
  | 86, 79 => contactPolynomial q 116
  | 86, 86 => contactPolynomial q 115
  | 86, 93 => contactPolynomial q 116
  | 87, 76 => contactPolynomial q 112
  | 87, 87 => contactPolynomial q 115
  | 87, 92 => contactPolynomial q 115
  | 88, 75 => contactPolynomial q 113
  | 88, 83 => contactPolynomial q 116
  | 88, 88 => contactPolynomial q 116
  | 89, 82 => contactPolynomial q 115
  | 89, 89 => contactPolynomial q 116
  | 89, 96 => contactPolynomial q 115
  | 90, 73 => contactPolynomial q 112
  | 90, 90 => contactPolynomial q 116
  | 90, 95 => contactPolynomial q 116
  | 91, 77 => contactPolynomial q 112
  | 91, 81 => contactPolynomial q 115
  | 91, 91 => contactPolynomial q 115
  | 92, 76 => contactPolynomial q 113
  | 92, 87 => contactPolynomial q 115
  | 92, 92 => contactPolynomial q 115
  | 93, 79 => contactPolynomial q 116
  | 93, 86 => contactPolynomial q 116
  | 93, 93 => contactPolynomial q 115
  | 94, 74 => contactPolynomial q 112
  | 94, 84 => contactPolynomial q 116
  | 94, 94 => contactPolynomial q 116
  | 95, 73 => contactPolynomial q 113
  | 95, 90 => contactPolynomial q 116
  | 95, 95 => contactPolynomial q 116
  | 96, 82 => contactPolynomial q 115
  | 96, 89 => contactPolynomial q 115
  | 96, 96 => contactPolynomial q 116
  | _, _ => 0

/-- No equality between the two matter momenta or their independent duals is imposed. -/
def actualContactTree (q pLeft pRight : Fin 4 → ℂ) : Module.End ℂ (Fock Mode) :=
  ∑ a : Fin 97, ∑ b : Fin 97,
    ((-1/2 : ℂ) * contactCoefficient q a b) •
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b)

theorem actual_contact_occupation (q pLeft pRight : Fin 4 → ℂ) :
    ActiveMatterSectorCharge.occupation * actualContactTree q pLeft pRight =
      actualContactTree q pLeft pRight * ActiveMatterSectorCharge.occupation := by
  have each (a b : Fin 97) : ActiveMatterSectorCharge.occupation *
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) =
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) *
        ActiveMatterSectorCharge.occupation :=
    LowEnergy.Fermion.occupationCharge_normalProduct _ _ _
      (actual_source_vertex_preserves pLeft a) (actual_source_vertex_preserves pRight b)
  simp only [actualContactTree, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, each]

theorem actual_contact_candidate_neutral (q pLeft pRight : Fin 4 → ℂ) (dual : Bool)
    (word : Occupation) (neutral : ∑ i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualContactTree q pLeft pRight (fiberCoordinates (candidate dual))) = 0 := by
  apply LowEnergy.Fermion.occupationCharge_selection modeWeight _
    (actual_contact_occupation q pLeft pRight)
    (fiberCoordinates (candidate dual)) (occupationBasis word)
    (if dual then (-3 : ℝ) else 3) 0
  · cases dual <;> norm_num
  · have h := actual_candidate_active_sector dual
    cases dual <;> simpa [ActiveMatterSectorCharge.occupation] using h
  · have h := SourceFockRaising.basis_eigenstate (fun i => (modeWeight i : ℂ)) word
    have hc : (∑ i ∈ word, (modeWeight i : ℂ)) = 0 := by exact_mod_cast neutral
    simpa only [hc, zero_smul, Complex.ofReal_zero] using h

theorem actual_contact_candidate_pure_four (q pLeft pRight : Fin 4 → ℂ) (dual : Bool)
    (word : Occupation) (pureFour : ∀ i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualContactTree q pLeft pRight (fiberCoordinates (candidate dual))) = 0 :=
  actual_contact_candidate_neutral q pLeft pRight dual word
    (Finset.sum_eq_zero fun i hi => pureFour i hi)

end LowEnergy.MixedSpectatorContactExchange
