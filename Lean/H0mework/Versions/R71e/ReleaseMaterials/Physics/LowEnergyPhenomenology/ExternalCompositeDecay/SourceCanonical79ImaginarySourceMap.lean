import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockImaginaryPoint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators Matrix

def sourcePolynomialPoint (negative : Bool) (a : Fin 16) : ℂ :=
  if negative then ![1, 0, (Real.sqrt 2 : ℂ), 0, 0, (-1 * Complex.I * (Real.sqrt 2 : ℂ)), 0, ((3/25) * Complex.I * (Real.sqrt 15 : ℂ)), ((-1/2) * Complex.I * (Real.sqrt 2 : ℂ)), 0, 0, ((-3/25) * Complex.I * (Real.sqrt 15 : ℂ)), ((3/25) * (Real.sqrt 15 : ℂ)), ((-1/2) * (Real.sqrt 2 : ℂ)), ((1/2) * (Real.sqrt 2 : ℂ)), ((-3/25) * (Real.sqrt 15 : ℂ))] a else
    ![1, 0, (Real.sqrt 2 : ℂ), 0, 0, (Complex.I * (Real.sqrt 2 : ℂ)), 0, ((-3/25) * Complex.I * (Real.sqrt 15 : ℂ)), ((1/2) * Complex.I * (Real.sqrt 2 : ℂ)), 0, 0, ((3/25) * Complex.I * (Real.sqrt 15 : ℂ)), ((3/25) * (Real.sqrt 15 : ℂ)), ((-1/2) * (Real.sqrt 2 : ℂ)), ((1/2) * (Real.sqrt 2 : ℂ)), ((-3/25) * (Real.sqrt 15 : ℂ))] a

def sourceSchema (v : Fin 16 → ℂ) (a : Fin 79) (b : Fin 97) : ℂ :=
  match a.val,b.val with
  | 0,9 => v 0
  | 1,10 => v 0
  | 2,11 => v 0
  | 3,12 => v 0
  | 4,13 => v 0
  | 5,14 => v 0
  | 6,15 => v 0
  | 7,16 => v 0
  | 8,17 => v 0
  | 9,18 => v 0
  | 10,19 => v 0
  | 11,20 => v 0
  | 12,21 => v 0
  | 13,22 => v 0
  | 14,23 => v 0
  | 15,24 => v 0
  | 16,25 => v 0
  | 17,26 => v 0
  | 18,27 => v 0
  | 19,28 => v 0
  | 20,29 => v 0
  | 21,30 => v 0
  | 22,31 => v 0
  | 23,32 => v 0
  | 24,33 => v 0
  | 25,34 => v 0
  | 26,35 => v 0
  | 27,36 => v 0
  | 28,37 => v 0
  | 29,38 => v 0
  | 30,39 => v 0
  | 31,40 => v 0
  | 32,41 => v 0
  | 33,42 => v 0
  | 34,43 => v 0
  | 35,44 => v 0
  | 36,45 => v 0
  | 37,46 => v 0
  | 38,47 => v 0
  | 39,48 => v 0
  | 40,49 => v 0
  | 41,50 => v 0
  | 42,51 => v 0
  | 43,52 => v 0
  | 44,53 => v 0
  | 45,54 => v 0
  | 46,55 => v 0
  | 47,56 => v 0
  | 48,57 => v 0
  | 48,75 => v 1
  | 49,61 => v 0
  | 49,76 => v 2
  | 49,77 => v 3
  | 49,81 => v 4
  | 49,91 => v 4
  | 50,62 => v 0
  | 50,79 => v 5
  | 50,82 => v 2
  | 50,83 => v 1
  | 51,65 => v 0
  | 51,76 => v 6
  | 51,77 => v 2
  | 51,87 => v 4
  | 51,92 => v 4
  | 52,66 => v 0
  | 52,78 => v 7
  | 52,80 => v 8
  | 52,82 => v 6
  | 52,83 => v 2
  | 52,85 => v 8
  | 52,89 => v 3
  | 52,96 => v 6
  | 53,67 => v 0
  | 53,86 => v 5
  | 53,88 => v 9
  | 53,89 => v 2
  | 54,69 => v 0
  | 54,78 => v 2
  | 54,93 => v 10
  | 55,70 => v 0
  | 55,77 => v 11
  | 55,81 => v 8
  | 55,84 => v 2
  | 55,91 => v 8
  | 55,95 => v 1
  | 56,71 => v 0
  | 56,76 => v 7
  | 56,87 => v 8
  | 56,90 => v 2
  | 56,92 => v 8
  | 56,94 => v 9
  | 57,72 => v 0
  | 57,93 => v 5
  | 57,96 => v 2
  | 58,78 => v 12
  | 58,80 => v 13
  | 58,82 => v 14
  | 58,85 => v 14
  | 58,89 => v 14
  | 58,96 => v 14
  | 60,78 => v 12
  | 60,80 => v 13
  | 60,82 => v 13
  | 60,85 => v 14
  | 60,89 => v 13
  | 60,96 => v 13
  | 61,76 => v 12
  | 61,87 => v 13
  | 61,92 => v 14
  | 63,76 => v 12
  | 63,87 => v 13
  | 63,92 => v 14
  | 64,78 => v 15
  | 64,80 => v 14
  | 64,82 => v 14
  | 64,85 => v 13
  | 64,89 => v 14
  | 64,96 => v 14
  | 66,78 => v 15
  | 66,80 => v 14
  | 66,82 => v 13
  | 66,85 => v 13
  | 66,89 => v 13
  | 66,96 => v 13
  | 67,76 => v 15
  | 67,87 => v 14
  | 67,92 => v 13
  | 71,77 => v 12
  | 71,81 => v 14
  | 71,91 => v 13
  | 73,77 => v 15
  | 73,81 => v 13
  | 73,91 => v 14
  | 77,77 => v 15
  | 77,81 => v 13
  | 77,91 => v 14
  | _,_ => 0

theorem actual_source_schema (x r : ℂ) (a : Fin 79) (b : Fin 97) :
    MixedSpectatorCanonical79Data.axialSourceMap x r a b =
      sourceSchema (MixedSpectatorCanonical79Data.sourceMapPolynomial x r) a b := by
  rfl

theorem actual_source_polynomial_point (negative : Bool) :
    MixedSpectatorCanonical79Data.sourceMapPolynomial
        (if negative then -Complex.I else Complex.I) 0 = sourcePolynomialPoint negative := by
  funext a
  cases negative <;> fin_cases a <;>
    norm_num [MixedSpectatorCanonical79Data.sourceMapPolynomial, sourcePolynomialPoint,
      Matrix.cons_val_zero, Matrix.cons_val_succ]

def sourceMapPoint (negative : Bool) : Matrix (Fin 79) (Fin 97) ℂ :=
  sourceSchema (sourcePolynomialPoint negative)

theorem actual_axial_source_point (negative : Bool) (a : Fin 79) (b : Fin 97) :
    MixedSpectatorCanonical79Data.axialSourceMap
        (if negative then -Complex.I else Complex.I) 0 a b = sourceMapPoint negative a b := by
  rw [actual_source_schema, actual_source_polynomial_point]
  rfl

theorem actual_world_source_point (negative : Bool) (a : Fin 79) (b : Fin 97) :
    MixedSpectatorCanonical79Exchange.worldSourceMap negative Complex.I 0 a b =
      sourceMapPoint negative a b := by
  classical
  simpa [MixedSpectatorCanonical79Exchange.worldSourceMap,
    ActualFourBlockElastic.zero_signed_radius,
    MixedSpectatorPairedSourceFrame.actual_zero_source_frame,Matrix.one_apply] using
      actual_axial_source_point negative a b

end LowEnergy.ActualCanonical79Imaginary
