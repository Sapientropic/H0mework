import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairData
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualContactDualImaginaryCoefficients
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra ActualContactDualImaginary MixedSpectatorContactExchange MixedSpectatorPairedSourceFrame
open scoped Matrix BigOperators

def contactBraRow0 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow1 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow2 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow3 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow4 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow5 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow6 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow7 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow8 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow9 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow9 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow9 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow10 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow10 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow10 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow11 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => _family 26
  | 11 => _family 27
  | 23 => _family 28
  | 26 => _family 29
  | 35 => _family 30
  | 37 => _family 31
  | 47 => _family 32
  | 48 => _family 29
  | _ => 0

def pointContactRow11 (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 11 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 26 => ((-3/20) * Complex.I)
  | 37 => ((3/20) * Complex.I)
  | 48 => ((-3/20) * Complex.I)
  | _ => 0

def contactBraRow11 (dual : Bool) : ℂ :=
  if dual then ((-7/500) * (Real.sqrt 30 : ℂ)) else ((-13/500) * (Real.sqrt 30 : ℂ))

def sourceContactRow12 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => _family 26
  | 12 => _family 27
  | 24 => _family 28
  | 25 => _family 31
  | 36 => _family 30
  | 38 => _family 31
  | 47 => _family 31
  | 48 => _family 32
  | _ => 0

def pointContactRow12 (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 12 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 25 => ((3/20) * Complex.I)
  | 38 => ((3/20) * Complex.I)
  | 47 => ((3/20) * Complex.I)
  | _ => 0

def contactBraRow12 (dual : Bool) : ℂ :=
  if dual then ((-7/500) * (Real.sqrt 30 : ℂ)) else ((-13/500) * (Real.sqrt 30 : ℂ))

def sourceContactRow13 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 2 => _family 26
  | 13 => _family 27
  | 24 => _family 29
  | 25 => _family 28
  | 35 => _family 29
  | 37 => _family 30
  | 49 => _family 32
  | 50 => _family 31
  | _ => 0

def pointContactRow13 (b : Fin 97) : ℂ :=
  match b.val with
  | 2 => ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 13 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 24 => ((-3/20) * Complex.I)
  | 35 => ((-3/20) * Complex.I)
  | 50 => ((3/20) * Complex.I)
  | _ => 0

def contactBraRow13 (dual : Bool) : ℂ :=
  if dual then ((-1/50) * (Real.sqrt 30 : ℂ)) else ((-1/50) * (Real.sqrt 30 : ℂ))

def sourceContactRow14 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 3 => _family 26
  | 14 => _family 27
  | 23 => _family 31
  | 26 => _family 28
  | 36 => _family 29
  | 38 => _family 30
  | 49 => _family 29
  | 50 => _family 32
  | _ => 0

def pointContactRow14 (b : Fin 97) : ℂ :=
  match b.val with
  | 3 => ((1/60) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 14 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 23 => ((3/20) * Complex.I)
  | 36 => ((-3/20) * Complex.I)
  | 49 => ((-3/20) * Complex.I)
  | _ => 0

def contactBraRow14 (dual : Bool) : ℂ :=
  if dual then ((-1/50) * (Real.sqrt 30 : ℂ)) else ((-1/50) * (Real.sqrt 30 : ℂ))

def sourceContactRow15 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 33
  | 7 => _family 12
  | 8 => _family 11
  | 15 => _family 34
  | 19 => _family 35
  | 20 => _family 36
  | 21 => _family 37
  | 27 => _family 38
  | 31 => _family 39
  | 32 => _family 40
  | 34 => _family 41
  | 39 => _family 42
  | 43 => _family 43
  | 44 => _family 44
  | 51 => _family 45
  | 55 => _family 46
  | 56 => _family 47
  | _ => 0

def pointContactRow15 (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => ((1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 7 => ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 8 => ((-1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 15 => ((-9/100) * (Real.sqrt 30 : ℂ))
  | 19 => ((-3/100) * (Real.sqrt 30 : ℂ))
  | 20 => ((3/100) * (Real.sqrt 30 : ℂ))
  | 21 => ((-9/40) * Complex.I)
  | 34 => ((9/40) * Complex.I)
  | _ => 0

def contactBraRow15 (dual : Bool) : ℂ :=
  if dual then ((-1/50) * (Real.sqrt 30 : ℂ)) else ((-1/50) * (Real.sqrt 30 : ℂ))

def sourceContactRow16 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow16 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow16 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow17 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow18 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow19 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 12
  | 7 => _family 33
  | 8 => _family 12
  | 15 => _family 35
  | 19 => _family 34
  | 20 => _family 35
  | 21 => _family 48
  | 27 => _family 39
  | 31 => _family 38
  | 32 => _family 39
  | 34 => _family 49
  | 39 => _family 43
  | 43 => _family 42
  | 44 => _family 43
  | 51 => _family 46
  | 55 => _family 45
  | 56 => _family 46
  | _ => 0

def pointContactRow19 (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 7 => ((1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 8 => ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 15 => ((-3/100) * (Real.sqrt 30 : ℂ))
  | 19 => ((-9/100) * (Real.sqrt 30 : ℂ))
  | 20 => ((-3/100) * (Real.sqrt 30 : ℂ))
  | 21 => ((-3/40) * Complex.I)
  | 34 => ((3/40) * Complex.I)
  | _ => 0

def contactBraRow19 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow20 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 11
  | 7 => _family 12
  | 8 => _family 33
  | 15 => _family 36
  | 19 => _family 35
  | 20 => _family 34
  | 21 => _family 49
  | 27 => _family 40
  | 31 => _family 39
  | 32 => _family 38
  | 34 => _family 48
  | 39 => _family 44
  | 43 => _family 43
  | 44 => _family 42
  | 51 => _family 47
  | 55 => _family 46
  | 56 => _family 45
  | _ => 0

def pointContactRow20 (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => ((-1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 7 => ((1/120) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 8 => ((1/40) * Complex.I * (Real.sqrt 15 : ℂ) * (Real.sqrt 30 : ℂ))
  | 15 => ((3/100) * (Real.sqrt 30 : ℂ))
  | 19 => ((-3/100) * (Real.sqrt 30 : ℂ))
  | 20 => ((-9/100) * (Real.sqrt 30 : ℂ))
  | 21 => ((3/40) * Complex.I)
  | 34 => ((-3/40) * Complex.I)
  | _ => 0

def contactBraRow20 (dual : Bool) : ℂ :=
  if dual then ((9/200) * (Real.sqrt 30 : ℂ)) else ((9/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow21 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 13
  | 7 => _family 24
  | 8 => _family 25
  | 15 => _family 41
  | 19 => _family 49
  | 20 => _family 48
  | 21 => _family 50
  | 27 => _family 51
  | 31 => _family 52
  | 32 => _family 53
  | 34 => _family 54
  | 39 => _family 55
  | 43 => _family 56
  | 44 => _family 57
  | 51 => _family 58
  | 55 => _family 59
  | 56 => _family 60
  | _ => 0

def pointContactRow21 (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => ((1/16) * (Real.sqrt 15 : ℂ))
  | 7 => ((1/48) * (Real.sqrt 15 : ℂ))
  | 8 => ((-1/48) * (Real.sqrt 15 : ℂ))
  | 15 => ((9/40) * Complex.I)
  | 19 => ((3/40) * Complex.I)
  | 20 => ((-3/40) * Complex.I)
  | 21 => ((-3/160) * (Real.sqrt 30 : ℂ))
  | 34 => ((3/160) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow21 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow22 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow22 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow22 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow23 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow24 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow25 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => _family 5
  | 2 => _family 61
  | 12 => _family 29
  | 13 => _family 28
  | 24 => _family 63
  | 25 => _family 62
  | 35 => _family 69
  | 36 => _family 67
  | 37 => _family 64
  | 38 => _family 72
  | 47 => _family 72
  | 48 => _family 70
  | 49 => _family 68
  | 50 => _family 66
  | _ => 0

def pointContactRow25 (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => ((-1/24) * (Real.sqrt 15 : ℂ))
  | 12 => ((-3/20) * Complex.I)
  | 25 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 38 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 47 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow25 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow26 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => _family 3
  | 3 => _family 61
  | 11 => _family 31
  | 14 => _family 28
  | 23 => _family 71
  | 26 => _family 62
  | 35 => _family 73
  | 36 => _family 69
  | 37 => _family 65
  | 38 => _family 64
  | 47 => _family 74
  | 48 => _family 72
  | 49 => _family 69
  | 50 => _family 68
  | _ => 0

def pointContactRow26 (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => ((1/24) * (Real.sqrt 15 : ℂ))
  | 11 => ((3/20) * Complex.I)
  | 26 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 37 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 48 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow26 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow27 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 75
  | 7 => _family 16
  | 8 => _family 15
  | 15 => _family 38
  | 19 => _family 39
  | 20 => _family 40
  | 21 => _family 76
  | 27 => _family 77
  | 31 => _family 78
  | 32 => _family 79
  | 34 => _family 51
  | 39 => _family 80
  | 43 => _family 81
  | 44 => _family 82
  | 51 => _family 83
  | 55 => _family 84
  | 56 => _family 85
  | _ => 0

def pointContactRow27 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow27 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow28 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow28 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow28 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow29 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow30 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow31 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 16
  | 7 => _family 75
  | 8 => _family 16
  | 15 => _family 39
  | 19 => _family 38
  | 20 => _family 39
  | 21 => _family 53
  | 27 => _family 78
  | 31 => _family 77
  | 32 => _family 78
  | 34 => _family 52
  | 39 => _family 81
  | 43 => _family 80
  | 44 => _family 81
  | 51 => _family 84
  | 55 => _family 83
  | 56 => _family 84
  | _ => 0

def pointContactRow31 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow31 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow32 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 15
  | 7 => _family 16
  | 8 => _family 75
  | 15 => _family 40
  | 19 => _family 39
  | 20 => _family 38
  | 21 => _family 52
  | 27 => _family 79
  | 31 => _family 78
  | 32 => _family 77
  | 34 => _family 53
  | 39 => _family 82
  | 43 => _family 81
  | 44 => _family 80
  | 51 => _family 85
  | 55 => _family 84
  | 56 => _family 83
  | _ => 0

def pointContactRow32 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow32 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow33 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow33 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow33 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow34 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 17
  | 7 => _family 25
  | 8 => _family 24
  | 15 => _family 37
  | 19 => _family 48
  | 20 => _family 49
  | 21 => _family 54
  | 27 => _family 76
  | 31 => _family 53
  | 32 => _family 52
  | 34 => _family 50
  | 39 => _family 87
  | 43 => _family 57
  | 44 => _family 56
  | 51 => _family 88
  | 55 => _family 60
  | 56 => _family 59
  | _ => 0

def pointContactRow34 (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => ((-1/16) * (Real.sqrt 15 : ℂ))
  | 7 => ((-1/48) * (Real.sqrt 15 : ℂ))
  | 8 => ((1/48) * (Real.sqrt 15 : ℂ))
  | 15 => ((-9/40) * Complex.I)
  | 19 => ((-3/40) * Complex.I)
  | 20 => ((3/40) * Complex.I)
  | 21 => ((3/160) * (Real.sqrt 30 : ℂ))
  | 34 => ((-3/160) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow34 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow35 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow36 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow37 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => _family 5
  | 2 => _family 89
  | 11 => _family 29
  | 13 => _family 30
  | 23 => _family 69
  | 24 => _family 67
  | 25 => _family 64
  | 26 => _family 65
  | 35 => _family 93
  | 37 => _family 90
  | 47 => _family 70
  | 48 => _family 65
  | 49 => _family 92
  | 50 => _family 73
  | _ => 0

def pointContactRow37 (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => ((-1/24) * (Real.sqrt 15 : ℂ))
  | 11 => ((-3/20) * Complex.I)
  | 26 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 37 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 48 => ((1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow37 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow38 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => _family 5
  | 3 => _family 89
  | 12 => _family 29
  | 14 => _family 30
  | 23 => _family 73
  | 24 => _family 69
  | 25 => _family 72
  | 26 => _family 64
  | 36 => _family 93
  | 38 => _family 90
  | 47 => _family 72
  | 48 => _family 70
  | 49 => _family 67
  | 50 => _family 92
  | _ => 0

def pointContactRow38 (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => ((-1/24) * (Real.sqrt 15 : ℂ))
  | 12 => ((-3/20) * Complex.I)
  | 25 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 38 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 47 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow38 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow39 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 94
  | 7 => _family 20
  | 8 => _family 19
  | 15 => _family 42
  | 19 => _family 43
  | 20 => _family 44
  | 21 => _family 87
  | 27 => _family 80
  | 31 => _family 81
  | 32 => _family 82
  | 34 => _family 55
  | 39 => _family 95
  | 43 => _family 96
  | 44 => _family 97
  | 51 => _family 98
  | 55 => _family 99
  | 56 => _family 100
  | _ => 0

def pointContactRow39 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow39 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow40 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow40 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow40 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow41 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow42 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow43 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 20
  | 7 => _family 94
  | 8 => _family 20
  | 15 => _family 43
  | 19 => _family 42
  | 20 => _family 43
  | 21 => _family 57
  | 27 => _family 81
  | 31 => _family 80
  | 32 => _family 81
  | 34 => _family 56
  | 39 => _family 96
  | 43 => _family 95
  | 44 => _family 96
  | 51 => _family 99
  | 55 => _family 98
  | 56 => _family 99
  | _ => 0

def pointContactRow43 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow43 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow44 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 19
  | 7 => _family 20
  | 8 => _family 94
  | 15 => _family 44
  | 19 => _family 43
  | 20 => _family 42
  | 21 => _family 56
  | 27 => _family 82
  | 31 => _family 81
  | 32 => _family 80
  | 34 => _family 57
  | 39 => _family 97
  | 43 => _family 96
  | 44 => _family 95
  | 51 => _family 100
  | 55 => _family 99
  | 56 => _family 98
  | _ => 0

def pointContactRow44 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow44 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow45 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow45 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow45 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow46 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow46 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow46 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow47 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => _family 102
  | 1 => _family 5
  | 11 => _family 32
  | 12 => _family 29
  | 23 => _family 68
  | 24 => _family 69
  | 25 => _family 72
  | 26 => _family 70
  | 35 => _family 92
  | 36 => _family 67
  | 37 => _family 74
  | 38 => _family 72
  | 47 => _family 103
  | 48 => _family 104
  | _ => 0

def pointContactRow47 (b : Fin 97) : ℂ :=
  match b.val with
  | 1 => ((-1/24) * (Real.sqrt 15 : ℂ))
  | 12 => ((-3/20) * Complex.I)
  | 25 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 38 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 47 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow47 (dual : Bool) : ℂ :=
  if dual then ((-21/5000) * (Real.sqrt 30 : ℂ)) else ((39/5000) * (Real.sqrt 30 : ℂ))

def sourceContactRow48 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => _family 3
  | 1 => _family 102
  | 11 => _family 31
  | 12 => _family 32
  | 23 => _family 66
  | 24 => _family 68
  | 25 => _family 74
  | 26 => _family 72
  | 35 => _family 73
  | 36 => _family 92
  | 37 => _family 65
  | 38 => _family 74
  | 47 => _family 105
  | 48 => _family 103
  | _ => 0

def pointContactRow48 (b : Fin 97) : ℂ :=
  match b.val with
  | 0 => ((1/24) * (Real.sqrt 15 : ℂ))
  | 11 => ((3/20) * Complex.I)
  | 26 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 37 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 48 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow48 (dual : Bool) : ℂ :=
  if dual then ((-21/5000) * (Real.sqrt 30 : ℂ)) else ((39/5000) * (Real.sqrt 30 : ℂ))

end LowEnergy.ActualBraContactDualContraction
