import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorContactVertices
import H0mework.Versions.R71e.Physics.LowEnergy.PacketField.Alignment

/-! Literal source97 restrictions of the paid all-angle field circles. The
paired Borel recipe is the original world_momentum source-generated frame. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorPairedSourceFrame
open scoped BigOperators Matrix

def circlePolynomial (z : ℝ) (a : Fin 33) : ℂ :=
  ![(1 * (z : ℂ)^0 + 2 * (z : ℂ)^2 + (-2) * (z : ℂ)^6 + (-1) * (z : ℂ)^8),
    ((-2) * (z : ℂ)^1 + (-6) * (z : ℂ)^3 + (-6) * (z : ℂ)^5 + (-2) * (z : ℂ)^7),
    (2 * (z : ℂ)^1 + 6 * (z : ℂ)^3 + 6 * (z : ℂ)^5 + 2 * (z : ℂ)^7),
    (1 * (z : ℂ)^0 + 4 * (z : ℂ)^2 + 6 * (z : ℂ)^4 + 4 * (z : ℂ)^6 + 1 * (z : ℂ)^8),
    (1 * (z : ℂ)^0 + (-4) * (z : ℂ)^2 + (-10) * (z : ℂ)^4 + (-4) * (z : ℂ)^6 + 1 * (z : ℂ)^8),
    (2 * (z : ℂ)^1 + 2 * (z : ℂ)^3 + (-2) * (z : ℂ)^5 + (-2) * (z : ℂ)^7),
    ((-2) * (z : ℂ)^1 + (-2) * (z : ℂ)^3 + 2 * (z : ℂ)^5 + 2 * (z : ℂ)^7),
    ((-4) * (z : ℂ)^1 + (-4) * (z : ℂ)^3 + 4 * (z : ℂ)^5 + 4 * (z : ℂ)^7),
    (1 * (z : ℂ)^0 + (-2) * (z : ℂ)^4 + 1 * (z : ℂ)^8),
    (4 * (z : ℂ)^2 + 8 * (z : ℂ)^4 + 4 * (z : ℂ)^6),
    (4 * (z : ℂ)^1 + 4 * (z : ℂ)^3 + (-4) * (z : ℂ)^5 + (-4) * (z : ℂ)^7),
    (1 * (z : ℂ)^0 + (-12) * (z : ℂ)^2 + 38 * (z : ℂ)^4 + (-12) * (z : ℂ)^6 + 1 * (z : ℂ)^8),
    (2 * (z : ℂ)^1 + (-14) * (z : ℂ)^3 + 14 * (z : ℂ)^5 + (-2) * (z : ℂ)^7),
    ((-2) * (z : ℂ)^1 + 14 * (z : ℂ)^3 + (-14) * (z : ℂ)^5 + 2 * (z : ℂ)^7),
    (4 * (z : ℂ)^1 + (-28) * (z : ℂ)^3 + 28 * (z : ℂ)^5 + (-4) * (z : ℂ)^7),
    (8 * (z : ℂ)^2 + (-16) * (z : ℂ)^4 + 8 * (z : ℂ)^6),
    ((-8) * (z : ℂ)^2 + 16 * (z : ℂ)^4 + (-8) * (z : ℂ)^6),
    (1 * (z : ℂ)^0 + (-6) * (z : ℂ)^2 + 6 * (z : ℂ)^6 + (-1) * (z : ℂ)^8),
    ((-2) * (z : ℂ)^1 + 10 * (z : ℂ)^3 + 10 * (z : ℂ)^5 + (-2) * (z : ℂ)^7),
    (4 * (z : ℂ)^1 + (-4) * (z : ℂ)^3 + (-4) * (z : ℂ)^5 + 4 * (z : ℂ)^7),
    ((-8) * (z : ℂ)^2 + 8 * (z : ℂ)^6),
    (2 * (z : ℂ)^1 + (-10) * (z : ℂ)^3 + (-10) * (z : ℂ)^5 + 2 * (z : ℂ)^7),
    (8 * (z : ℂ)^2 + (-8) * (z : ℂ)^6),
    ((-4) * (z : ℂ)^1 + 28 * (z : ℂ)^3 + (-28) * (z : ℂ)^5 + 4 * (z : ℂ)^7),
    (1 * (z : ℂ)^0 + (-8) * (z : ℂ)^2 + 14 * (z : ℂ)^4 + (-8) * (z : ℂ)^6 + 1 * (z : ℂ)^8),
    (4 * (z : ℂ)^2 + (-24) * (z : ℂ)^4 + 4 * (z : ℂ)^6),
    ((-16) * (z : ℂ)^2 + 32 * (z : ℂ)^4 + (-16) * (z : ℂ)^6),
    (4 * (z : ℂ)^1 + (-12) * (z : ℂ)^3 + 12 * (z : ℂ)^5 + (-4) * (z : ℂ)^7),
    (16 * (z : ℂ)^3 + (-16) * (z : ℂ)^5),
    (16 * (z : ℂ)^2 + (-32) * (z : ℂ)^4 + 16 * (z : ℂ)^6),
    ((-4) * (z : ℂ)^1 + 4 * (z : ℂ)^3 + 4 * (z : ℂ)^5 + (-4) * (z : ℂ)^7),
    ((-4) * (z : ℂ)^1 + 12 * (z : ℂ)^3 + (-12) * (z : ℂ)^5 + 4 * (z : ℂ)^7),
    ((-16) * (z : ℂ)^3 + 16 * (z : ℂ)^5)] a

def circleNumerator (axis : Fin 2) (z : ℝ) (a b : Fin 97) : ℂ :=
  match axis.val, a.val, b.val with
  | 0, 0, 0 => circlePolynomial z 0
  | 0, 0, 2 => circlePolynomial z 1
  | 0, 1, 1 => circlePolynomial z 0
  | 0, 1, 3 => circlePolynomial z 1
  | 0, 2, 0 => circlePolynomial z 2
  | 0, 2, 2 => circlePolynomial z 0
  | 0, 3, 1 => circlePolynomial z 2
  | 0, 3, 3 => circlePolynomial z 0
  | 0, 4, 4 => circlePolynomial z 3
  | 0, 5, 5 => circlePolynomial z 3
  | 0, 6, 6 => circlePolynomial z 3
  | 0, 7, 7 => circlePolynomial z 3
  | 0, 8, 8 => circlePolynomial z 3
  | 0, 9, 9 => circlePolynomial z 3
  | 0, 10, 10 => circlePolynomial z 4
  | 0, 10, 15 => circlePolynomial z 5
  | 0, 10, 16 => circlePolynomial z 6
  | 0, 11, 11 => circlePolynomial z 0
  | 0, 11, 13 => circlePolynomial z 1
  | 0, 12, 12 => circlePolynomial z 0
  | 0, 12, 14 => circlePolynomial z 1
  | 0, 13, 11 => circlePolynomial z 2
  | 0, 13, 13 => circlePolynomial z 0
  | 0, 14, 12 => circlePolynomial z 2
  | 0, 14, 14 => circlePolynomial z 0
  | 0, 15, 10 => circlePolynomial z 7
  | 0, 15, 15 => circlePolynomial z 8
  | 0, 15, 16 => circlePolynomial z 9
  | 0, 16, 10 => circlePolynomial z 10
  | 0, 16, 15 => circlePolynomial z 9
  | 0, 16, 16 => circlePolynomial z 8
  | 0, 17, 17 => circlePolynomial z 3
  | 0, 18, 18 => circlePolynomial z 3
  | 0, 19, 19 => circlePolynomial z 3
  | 0, 20, 20 => circlePolynomial z 3
  | 0, 21, 21 => circlePolynomial z 4
  | 0, 21, 45 => circlePolynomial z 10
  | 0, 22, 22 => circlePolynomial z 11
  | 0, 22, 27 => circlePolynomial z 12
  | 0, 22, 28 => circlePolynomial z 13
  | 0, 22, 46 => circlePolynomial z 14
  | 0, 22, 51 => circlePolynomial z 15
  | 0, 22, 52 => circlePolynomial z 16
  | 0, 23, 23 => circlePolynomial z 17
  | 0, 23, 25 => circlePolynomial z 18
  | 0, 23, 47 => circlePolynomial z 19
  | 0, 23, 49 => circlePolynomial z 20
  | 0, 24, 24 => circlePolynomial z 17
  | 0, 24, 26 => circlePolynomial z 18
  | 0, 24, 48 => circlePolynomial z 19
  | 0, 24, 50 => circlePolynomial z 20
  | 0, 25, 23 => circlePolynomial z 21
  | 0, 25, 25 => circlePolynomial z 17
  | 0, 25, 47 => circlePolynomial z 22
  | 0, 25, 49 => circlePolynomial z 19
  | 0, 26, 24 => circlePolynomial z 21
  | 0, 26, 26 => circlePolynomial z 17
  | 0, 26, 48 => circlePolynomial z 22
  | 0, 26, 50 => circlePolynomial z 19
  | 0, 27, 22 => circlePolynomial z 23
  | 0, 27, 27 => circlePolynomial z 24
  | 0, 27, 28 => circlePolynomial z 25
  | 0, 27, 46 => circlePolynomial z 26
  | 0, 27, 51 => circlePolynomial z 27
  | 0, 27, 52 => circlePolynomial z 28
  | 0, 28, 22 => circlePolynomial z 14
  | 0, 28, 27 => circlePolynomial z 25
  | 0, 28, 28 => circlePolynomial z 24
  | 0, 28, 46 => circlePolynomial z 29
  | 0, 28, 51 => circlePolynomial z 28
  | 0, 28, 52 => circlePolynomial z 27
  | 0, 29, 29 => circlePolynomial z 4
  | 0, 29, 53 => circlePolynomial z 10
  | 0, 30, 30 => circlePolynomial z 4
  | 0, 30, 54 => circlePolynomial z 10
  | 0, 31, 31 => circlePolynomial z 4
  | 0, 31, 55 => circlePolynomial z 10
  | 0, 32, 32 => circlePolynomial z 4
  | 0, 32, 56 => circlePolynomial z 10
  | 0, 33, 33 => circlePolynomial z 3
  | 0, 34, 34 => circlePolynomial z 4
  | 0, 34, 39 => circlePolynomial z 5
  | 0, 34, 40 => circlePolynomial z 6
  | 0, 35, 35 => circlePolynomial z 0
  | 0, 35, 37 => circlePolynomial z 1
  | 0, 36, 36 => circlePolynomial z 0
  | 0, 36, 38 => circlePolynomial z 1
  | 0, 37, 35 => circlePolynomial z 2
  | 0, 37, 37 => circlePolynomial z 0
  | 0, 38, 36 => circlePolynomial z 2
  | 0, 38, 38 => circlePolynomial z 0
  | 0, 39, 34 => circlePolynomial z 7
  | 0, 39, 39 => circlePolynomial z 8
  | 0, 39, 40 => circlePolynomial z 9
  | 0, 40, 34 => circlePolynomial z 10
  | 0, 40, 39 => circlePolynomial z 9
  | 0, 40, 40 => circlePolynomial z 8
  | 0, 41, 41 => circlePolynomial z 3
  | 0, 42, 42 => circlePolynomial z 3
  | 0, 43, 43 => circlePolynomial z 3
  | 0, 44, 44 => circlePolynomial z 3
  | 0, 45, 21 => circlePolynomial z 7
  | 0, 45, 45 => circlePolynomial z 4
  | 0, 46, 22 => circlePolynomial z 23
  | 0, 46, 27 => circlePolynomial z 16
  | 0, 46, 28 => circlePolynomial z 15
  | 0, 46, 46 => circlePolynomial z 11
  | 0, 46, 51 => circlePolynomial z 12
  | 0, 46, 52 => circlePolynomial z 13
  | 0, 47, 23 => circlePolynomial z 30
  | 0, 47, 25 => circlePolynomial z 22
  | 0, 47, 47 => circlePolynomial z 17
  | 0, 47, 49 => circlePolynomial z 18
  | 0, 48, 24 => circlePolynomial z 30
  | 0, 48, 26 => circlePolynomial z 22
  | 0, 48, 48 => circlePolynomial z 17
  | 0, 48, 50 => circlePolynomial z 18
  | 0, 49, 23 => circlePolynomial z 20
  | 0, 49, 25 => circlePolynomial z 30
  | 0, 49, 47 => circlePolynomial z 21
  | 0, 49, 49 => circlePolynomial z 17
  | 0, 50, 24 => circlePolynomial z 20
  | 0, 50, 26 => circlePolynomial z 30
  | 0, 50, 48 => circlePolynomial z 21
  | 0, 50, 50 => circlePolynomial z 17
  | 0, 51, 22 => circlePolynomial z 29
  | 0, 51, 27 => circlePolynomial z 31
  | 0, 51, 28 => circlePolynomial z 32
  | 0, 51, 46 => circlePolynomial z 23
  | 0, 51, 51 => circlePolynomial z 24
  | 0, 51, 52 => circlePolynomial z 25
  | 0, 52, 22 => circlePolynomial z 26
  | 0, 52, 27 => circlePolynomial z 32
  | 0, 52, 28 => circlePolynomial z 31
  | 0, 52, 46 => circlePolynomial z 14
  | 0, 52, 51 => circlePolynomial z 25
  | 0, 52, 52 => circlePolynomial z 24
  | 0, 53, 29 => circlePolynomial z 7
  | 0, 53, 53 => circlePolynomial z 4
  | 0, 54, 30 => circlePolynomial z 7
  | 0, 54, 54 => circlePolynomial z 4
  | 0, 55, 31 => circlePolynomial z 7
  | 0, 55, 55 => circlePolynomial z 4
  | 0, 56, 32 => circlePolynomial z 7
  | 0, 56, 56 => circlePolynomial z 4
  | 0, 57, 57 => circlePolynomial z 3
  | 0, 58, 58 => circlePolynomial z 4
  | 0, 58, 60 => circlePolynomial z 10
  | 0, 59, 59 => circlePolynomial z 3
  | 0, 60, 58 => circlePolynomial z 7
  | 0, 60, 60 => circlePolynomial z 4
  | 0, 61, 61 => circlePolynomial z 4
  | 0, 61, 69 => circlePolynomial z 10
  | 0, 62, 62 => circlePolynomial z 11
  | 0, 62, 64 => circlePolynomial z 14
  | 0, 62, 70 => circlePolynomial z 14
  | 0, 62, 72 => circlePolynomial z 29
  | 0, 63, 63 => circlePolynomial z 4
  | 0, 63, 71 => circlePolynomial z 10
  | 0, 64, 62 => circlePolynomial z 23
  | 0, 64, 64 => circlePolynomial z 11
  | 0, 64, 70 => circlePolynomial z 26
  | 0, 64, 72 => circlePolynomial z 14
  | 0, 65, 65 => circlePolynomial z 3
  | 0, 66, 66 => circlePolynomial z 4
  | 0, 66, 68 => circlePolynomial z 10
  | 0, 67, 67 => circlePolynomial z 3
  | 0, 68, 66 => circlePolynomial z 7
  | 0, 68, 68 => circlePolynomial z 4
  | 0, 69, 61 => circlePolynomial z 7
  | 0, 69, 69 => circlePolynomial z 4
  | 0, 70, 62 => circlePolynomial z 23
  | 0, 70, 64 => circlePolynomial z 26
  | 0, 70, 70 => circlePolynomial z 11
  | 0, 70, 72 => circlePolynomial z 14
  | 0, 71, 63 => circlePolynomial z 7
  | 0, 71, 71 => circlePolynomial z 4
  | 0, 72, 62 => circlePolynomial z 29
  | 0, 72, 64 => circlePolynomial z 23
  | 0, 72, 70 => circlePolynomial z 23
  | 0, 72, 72 => circlePolynomial z 11
  | 0, 73, 73 => circlePolynomial z 4
  | 0, 73, 75 => circlePolynomial z 10
  | 0, 74, 74 => circlePolynomial z 3
  | 0, 75, 73 => circlePolynomial z 7
  | 0, 75, 75 => circlePolynomial z 4
  | 0, 76, 76 => circlePolynomial z 4
  | 0, 76, 78 => circlePolynomial z 10
  | 0, 77, 77 => circlePolynomial z 3
  | 0, 78, 76 => circlePolynomial z 7
  | 0, 78, 78 => circlePolynomial z 4
  | 0, 79, 79 => circlePolynomial z 11
  | 0, 79, 81 => circlePolynomial z 14
  | 0, 79, 91 => circlePolynomial z 14
  | 0, 79, 93 => circlePolynomial z 29
  | 0, 80, 80 => circlePolynomial z 4
  | 0, 80, 92 => circlePolynomial z 10
  | 0, 81, 79 => circlePolynomial z 23
  | 0, 81, 81 => circlePolynomial z 11
  | 0, 81, 91 => circlePolynomial z 26
  | 0, 81, 93 => circlePolynomial z 14
  | 0, 82, 82 => circlePolynomial z 11
  | 0, 82, 84 => circlePolynomial z 14
  | 0, 82, 94 => circlePolynomial z 14
  | 0, 82, 96 => circlePolynomial z 29
  | 0, 83, 83 => circlePolynomial z 4
  | 0, 83, 95 => circlePolynomial z 10
  | 0, 84, 82 => circlePolynomial z 23
  | 0, 84, 84 => circlePolynomial z 11
  | 0, 84, 94 => circlePolynomial z 26
  | 0, 84, 96 => circlePolynomial z 14
  | 0, 85, 85 => circlePolynomial z 4
  | 0, 85, 87 => circlePolynomial z 10
  | 0, 86, 86 => circlePolynomial z 3
  | 0, 87, 85 => circlePolynomial z 7
  | 0, 87, 87 => circlePolynomial z 4
  | 0, 88, 88 => circlePolynomial z 4
  | 0, 88, 90 => circlePolynomial z 10
  | 0, 89, 89 => circlePolynomial z 3
  | 0, 90, 88 => circlePolynomial z 7
  | 0, 90, 90 => circlePolynomial z 4
  | 0, 91, 79 => circlePolynomial z 23
  | 0, 91, 81 => circlePolynomial z 26
  | 0, 91, 91 => circlePolynomial z 11
  | 0, 91, 93 => circlePolynomial z 14
  | 0, 92, 80 => circlePolynomial z 7
  | 0, 92, 92 => circlePolynomial z 4
  | 0, 93, 79 => circlePolynomial z 29
  | 0, 93, 81 => circlePolynomial z 23
  | 0, 93, 91 => circlePolynomial z 23
  | 0, 93, 93 => circlePolynomial z 11
  | 0, 94, 82 => circlePolynomial z 23
  | 0, 94, 84 => circlePolynomial z 26
  | 0, 94, 94 => circlePolynomial z 11
  | 0, 94, 96 => circlePolynomial z 14
  | 0, 95, 83 => circlePolynomial z 7
  | 0, 95, 95 => circlePolynomial z 4
  | 0, 96, 82 => circlePolynomial z 29
  | 0, 96, 84 => circlePolynomial z 23
  | 0, 96, 94 => circlePolynomial z 23
  | 0, 96, 96 => circlePolynomial z 11
  | 1, 0, 0 => circlePolynomial z 0
  | 1, 0, 1 => circlePolynomial z 2
  | 1, 1, 0 => circlePolynomial z 1
  | 1, 1, 1 => circlePolynomial z 0
  | 1, 2, 2 => circlePolynomial z 0
  | 1, 2, 3 => circlePolynomial z 1
  | 1, 3, 2 => circlePolynomial z 2
  | 1, 3, 3 => circlePolynomial z 0
  | 1, 4, 4 => circlePolynomial z 3
  | 1, 5, 5 => circlePolynomial z 3
  | 1, 6, 6 => circlePolynomial z 3
  | 1, 7, 7 => circlePolynomial z 3
  | 1, 8, 8 => circlePolynomial z 3
  | 1, 9, 9 => circlePolynomial z 4
  | 1, 9, 10 => circlePolynomial z 10
  | 1, 10, 9 => circlePolynomial z 7
  | 1, 10, 10 => circlePolynomial z 4
  | 1, 11, 11 => circlePolynomial z 0
  | 1, 11, 12 => circlePolynomial z 2
  | 1, 12, 11 => circlePolynomial z 1
  | 1, 12, 12 => circlePolynomial z 0
  | 1, 13, 13 => circlePolynomial z 0
  | 1, 13, 14 => circlePolynomial z 1
  | 1, 14, 13 => circlePolynomial z 2
  | 1, 14, 14 => circlePolynomial z 0
  | 1, 15, 15 => circlePolynomial z 3
  | 1, 16, 16 => circlePolynomial z 3
  | 1, 17, 17 => circlePolynomial z 3
  | 1, 18, 18 => circlePolynomial z 3
  | 1, 19, 19 => circlePolynomial z 3
  | 1, 20, 20 => circlePolynomial z 3
  | 1, 21, 21 => circlePolynomial z 11
  | 1, 21, 22 => circlePolynomial z 14
  | 1, 21, 33 => circlePolynomial z 23
  | 1, 21, 34 => circlePolynomial z 26
  | 1, 22, 21 => circlePolynomial z 23
  | 1, 22, 22 => circlePolynomial z 11
  | 1, 22, 33 => circlePolynomial z 29
  | 1, 22, 34 => circlePolynomial z 23
  | 1, 23, 23 => circlePolynomial z 17
  | 1, 23, 24 => circlePolynomial z 21
  | 1, 23, 35 => circlePolynomial z 30
  | 1, 23, 36 => circlePolynomial z 20
  | 1, 24, 23 => circlePolynomial z 18
  | 1, 24, 24 => circlePolynomial z 17
  | 1, 24, 35 => circlePolynomial z 22
  | 1, 24, 36 => circlePolynomial z 30
  | 1, 25, 25 => circlePolynomial z 17
  | 1, 25, 26 => circlePolynomial z 18
  | 1, 25, 37 => circlePolynomial z 30
  | 1, 25, 38 => circlePolynomial z 22
  | 1, 26, 25 => circlePolynomial z 21
  | 1, 26, 26 => circlePolynomial z 17
  | 1, 26, 37 => circlePolynomial z 20
  | 1, 26, 38 => circlePolynomial z 30
  | 1, 27, 27 => circlePolynomial z 4
  | 1, 27, 39 => circlePolynomial z 7
  | 1, 28, 28 => circlePolynomial z 4
  | 1, 28, 40 => circlePolynomial z 7
  | 1, 29, 29 => circlePolynomial z 4
  | 1, 29, 41 => circlePolynomial z 7
  | 1, 30, 30 => circlePolynomial z 4
  | 1, 30, 42 => circlePolynomial z 7
  | 1, 31, 31 => circlePolynomial z 4
  | 1, 31, 43 => circlePolynomial z 7
  | 1, 32, 32 => circlePolynomial z 4
  | 1, 32, 44 => circlePolynomial z 7
  | 1, 33, 21 => circlePolynomial z 14
  | 1, 33, 22 => circlePolynomial z 29
  | 1, 33, 33 => circlePolynomial z 11
  | 1, 33, 34 => circlePolynomial z 14
  | 1, 34, 21 => circlePolynomial z 26
  | 1, 34, 22 => circlePolynomial z 14
  | 1, 34, 33 => circlePolynomial z 23
  | 1, 34, 34 => circlePolynomial z 11
  | 1, 35, 23 => circlePolynomial z 19
  | 1, 35, 24 => circlePolynomial z 22
  | 1, 35, 35 => circlePolynomial z 17
  | 1, 35, 36 => circlePolynomial z 21
  | 1, 36, 23 => circlePolynomial z 20
  | 1, 36, 24 => circlePolynomial z 19
  | 1, 36, 35 => circlePolynomial z 18
  | 1, 36, 36 => circlePolynomial z 17
  | 1, 37, 25 => circlePolynomial z 19
  | 1, 37, 26 => circlePolynomial z 20
  | 1, 37, 37 => circlePolynomial z 17
  | 1, 37, 38 => circlePolynomial z 18
  | 1, 38, 25 => circlePolynomial z 22
  | 1, 38, 26 => circlePolynomial z 19
  | 1, 38, 37 => circlePolynomial z 21
  | 1, 38, 38 => circlePolynomial z 17
  | 1, 39, 27 => circlePolynomial z 10
  | 1, 39, 39 => circlePolynomial z 4
  | 1, 40, 28 => circlePolynomial z 10
  | 1, 40, 40 => circlePolynomial z 4
  | 1, 41, 29 => circlePolynomial z 10
  | 1, 41, 41 => circlePolynomial z 4
  | 1, 42, 30 => circlePolynomial z 10
  | 1, 42, 42 => circlePolynomial z 4
  | 1, 43, 31 => circlePolynomial z 10
  | 1, 43, 43 => circlePolynomial z 4
  | 1, 44, 32 => circlePolynomial z 10
  | 1, 44, 44 => circlePolynomial z 4
  | 1, 45, 45 => circlePolynomial z 4
  | 1, 45, 46 => circlePolynomial z 10
  | 1, 46, 45 => circlePolynomial z 7
  | 1, 46, 46 => circlePolynomial z 4
  | 1, 47, 47 => circlePolynomial z 0
  | 1, 47, 48 => circlePolynomial z 2
  | 1, 48, 47 => circlePolynomial z 1
  | 1, 48, 48 => circlePolynomial z 0
  | 1, 49, 49 => circlePolynomial z 0
  | 1, 49, 50 => circlePolynomial z 1
  | 1, 50, 49 => circlePolynomial z 2
  | 1, 50, 50 => circlePolynomial z 0
  | 1, 51, 51 => circlePolynomial z 3
  | 1, 52, 52 => circlePolynomial z 3
  | 1, 53, 53 => circlePolynomial z 3
  | 1, 54, 54 => circlePolynomial z 3
  | 1, 55, 55 => circlePolynomial z 3
  | 1, 56, 56 => circlePolynomial z 3
  | 1, 57, 57 => circlePolynomial z 3
  | 1, 58, 58 => circlePolynomial z 4
  | 1, 58, 59 => circlePolynomial z 7
  | 1, 59, 58 => circlePolynomial z 10
  | 1, 59, 59 => circlePolynomial z 4
  | 1, 60, 60 => circlePolynomial z 3
  | 1, 61, 61 => circlePolynomial z 4
  | 1, 61, 65 => circlePolynomial z 7
  | 1, 62, 62 => circlePolynomial z 11
  | 1, 62, 63 => circlePolynomial z 23
  | 1, 62, 66 => circlePolynomial z 23
  | 1, 62, 67 => circlePolynomial z 29
  | 1, 63, 62 => circlePolynomial z 14
  | 1, 63, 63 => circlePolynomial z 11
  | 1, 63, 66 => circlePolynomial z 26
  | 1, 63, 67 => circlePolynomial z 23
  | 1, 64, 64 => circlePolynomial z 4
  | 1, 64, 68 => circlePolynomial z 7
  | 1, 65, 61 => circlePolynomial z 10
  | 1, 65, 65 => circlePolynomial z 4
  | 1, 66, 62 => circlePolynomial z 14
  | 1, 66, 63 => circlePolynomial z 26
  | 1, 66, 66 => circlePolynomial z 11
  | 1, 66, 67 => circlePolynomial z 23
  | 1, 67, 62 => circlePolynomial z 29
  | 1, 67, 63 => circlePolynomial z 14
  | 1, 67, 66 => circlePolynomial z 14
  | 1, 67, 67 => circlePolynomial z 11
  | 1, 68, 64 => circlePolynomial z 10
  | 1, 68, 68 => circlePolynomial z 4
  | 1, 69, 69 => circlePolynomial z 3
  | 1, 70, 70 => circlePolynomial z 4
  | 1, 70, 71 => circlePolynomial z 7
  | 1, 71, 70 => circlePolynomial z 10
  | 1, 71, 71 => circlePolynomial z 4
  | 1, 72, 72 => circlePolynomial z 3
  | 1, 73, 73 => circlePolynomial z 4
  | 1, 73, 74 => circlePolynomial z 7
  | 1, 74, 73 => circlePolynomial z 10
  | 1, 74, 74 => circlePolynomial z 4
  | 1, 75, 75 => circlePolynomial z 3
  | 1, 76, 76 => circlePolynomial z 4
  | 1, 76, 77 => circlePolynomial z 7
  | 1, 77, 76 => circlePolynomial z 10
  | 1, 77, 77 => circlePolynomial z 4
  | 1, 78, 78 => circlePolynomial z 3
  | 1, 79, 79 => circlePolynomial z 11
  | 1, 79, 80 => circlePolynomial z 23
  | 1, 79, 85 => circlePolynomial z 23
  | 1, 79, 86 => circlePolynomial z 29
  | 1, 80, 79 => circlePolynomial z 14
  | 1, 80, 80 => circlePolynomial z 11
  | 1, 80, 85 => circlePolynomial z 26
  | 1, 80, 86 => circlePolynomial z 23
  | 1, 81, 81 => circlePolynomial z 4
  | 1, 81, 87 => circlePolynomial z 7
  | 1, 82, 82 => circlePolynomial z 11
  | 1, 82, 83 => circlePolynomial z 23
  | 1, 82, 88 => circlePolynomial z 23
  | 1, 82, 89 => circlePolynomial z 29
  | 1, 83, 82 => circlePolynomial z 14
  | 1, 83, 83 => circlePolynomial z 11
  | 1, 83, 88 => circlePolynomial z 26
  | 1, 83, 89 => circlePolynomial z 23
  | 1, 84, 84 => circlePolynomial z 4
  | 1, 84, 90 => circlePolynomial z 7
  | 1, 85, 79 => circlePolynomial z 14
  | 1, 85, 80 => circlePolynomial z 26
  | 1, 85, 85 => circlePolynomial z 11
  | 1, 85, 86 => circlePolynomial z 23
  | 1, 86, 79 => circlePolynomial z 29
  | 1, 86, 80 => circlePolynomial z 14
  | 1, 86, 85 => circlePolynomial z 14
  | 1, 86, 86 => circlePolynomial z 11
  | 1, 87, 81 => circlePolynomial z 10
  | 1, 87, 87 => circlePolynomial z 4
  | 1, 88, 82 => circlePolynomial z 14
  | 1, 88, 83 => circlePolynomial z 26
  | 1, 88, 88 => circlePolynomial z 11
  | 1, 88, 89 => circlePolynomial z 23
  | 1, 89, 82 => circlePolynomial z 29
  | 1, 89, 83 => circlePolynomial z 14
  | 1, 89, 88 => circlePolynomial z 14
  | 1, 89, 89 => circlePolynomial z 11
  | 1, 90, 84 => circlePolynomial z 10
  | 1, 90, 90 => circlePolynomial z 4
  | 1, 91, 91 => circlePolynomial z 4
  | 1, 91, 92 => circlePolynomial z 7
  | 1, 92, 91 => circlePolynomial z 10
  | 1, 92, 92 => circlePolynomial z 4
  | 1, 93, 93 => circlePolynomial z 3
  | 1, 94, 94 => circlePolynomial z 4
  | 1, 94, 95 => circlePolynomial z 7
  | 1, 95, 94 => circlePolynomial z 10
  | 1, 95, 95 => circlePolynomial z 4
  | 1, 96, 96 => circlePolynomial z 3
  | _, _, _ => 0

def circle (axis : Fin 2) (z : ℝ) : Matrix (Fin 97) (Fin 97) ℂ :=
  fun a b => circleNumerator axis z a b / (((1+z^2)^4 : ℝ) : ℂ)

abbrev lineSign := SaturationMonoid.PhysicsCore.LowEnergy.PacketField.lineSign
abbrev spatialRadius := SaturationMonoid.PhysicsCore.LowEnergy.Rotation.momentumRadius

def signedRadius (k : Fin 3 → ℝ) : ℝ := lineSign k * spatialRadius k / Real.sqrt 2

def parameterY (k : Fin 3 → ℝ) : ℝ :=
  (SaturationMonoid.PhysicsCore.LowEnergy.PacketField.pairedParameters k).1

def parameterZ (k : Fin 3 → ℝ) : ℝ :=
  (SaturationMonoid.PhysicsCore.LowEnergy.PacketField.pairedParameters k).2

def zeroSpatial (k : Fin 3 → ℝ) : Prop := k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0

def pairedSourceFrame (k : Fin 3 → ℝ) : Matrix (Fin 97) (Fin 97) ℂ := by
  classical
  exact if zeroSpatial k then 1 else circle 1 (parameterZ k) * circle 0 (parameterY k)

def pairedSourceInverse (k : Fin 3 → ℝ) : Matrix (Fin 97) (Fin 97) ℂ := by
  classical
  exact if zeroSpatial k then 1 else circle 0 (-parameterY k) * circle 1 (-parameterZ k)

theorem actual_parameters_negative (k : Fin 3 → ℝ) :
    parameterY (-k) = parameterY k ∧ parameterZ (-k) = parameterZ k := by
  have h := SaturationMonoid.PhysicsCore.LowEnergy.PacketField.pairedParameters_negative k
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

theorem actual_source_frame_negative (k : Fin 3 → ℝ) : pairedSourceFrame (-k) = pairedSourceFrame k := by
  classical
  obtain ⟨hy,hz⟩ := actual_parameters_negative k
  have he : zeroSpatial (-k) ↔ zeroSpatial k := by
    simp only [zeroSpatial,Pi.neg_apply,neg_eq_zero]
  unfold pairedSourceFrame
  by_cases h : zeroSpatial k
  · rw [if_pos (he.mpr h),if_pos h]
  · rw [if_neg (fun hn => h (he.mp hn)),if_neg h,hy,hz]

theorem actual_zero_source_frame : pairedSourceFrame 0 = 1 := by
  classical
  simp [pairedSourceFrame,zeroSpatial]

/-- The physical Fourier transfer of the original world producer. -/
def worldTransfer (x : ℂ) (k : Fin 3 → ℝ) : Fin 4 → ℂ :=
  ![(6 * (Real.sqrt 15 : ℂ) / 25) * x, Complex.I * k 0, Complex.I * k 1, Complex.I * k 2]

end LowEnergy.MixedSpectatorPairedSourceFrame
