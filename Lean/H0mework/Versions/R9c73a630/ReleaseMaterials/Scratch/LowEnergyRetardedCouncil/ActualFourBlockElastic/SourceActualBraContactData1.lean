import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactData0
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

def sourceContactRow49 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 2 => _family 102
  | 3 => _family 3
  | 13 => _family 32
  | 14 => _family 31
  | 23 => _family 65
  | 24 => _family 70
  | 25 => _family 68
  | 26 => _family 66
  | 35 => _family 70
  | 36 => _family 72
  | 37 => _family 92
  | 38 => _family 73
  | 49 => _family 103
  | 50 => _family 105
  | _ => 0

def pointContactRow49 (b : Fin 97) : ℂ :=
  match b.val with
  | 3 => ((1/24) * (Real.sqrt 15 : ℂ))
  | 14 => ((3/20) * Complex.I)
  | 23 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 36 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | 49 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow49 (dual : Bool) : ℂ :=
  if dual then ((-9/5000) * (Real.sqrt 30 : ℂ)) else ((-9/5000) * (Real.sqrt 30 : ℂ))

def sourceContactRow50 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 2 => _family 5
  | 3 => _family 102
  | 13 => _family 29
  | 14 => _family 32
  | 23 => _family 74
  | 24 => _family 65
  | 25 => _family 69
  | 26 => _family 68
  | 35 => _family 65
  | 36 => _family 70
  | 37 => _family 67
  | 38 => _family 92
  | 49 => _family 104
  | 50 => _family 103
  | _ => 0

def pointContactRow50 (b : Fin 97) : ℂ :=
  match b.val with
  | 2 => ((-1/24) * (Real.sqrt 15 : ℂ))
  | 13 => ((-3/20) * Complex.I)
  | 24 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 35 => ((1/80) * (Real.sqrt 30 : ℂ))
  | 50 => ((-1/80) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow50 (dual : Bool) : ℂ :=
  if dual then ((-9/5000) * (Real.sqrt 30 : ℂ)) else ((-9/5000) * (Real.sqrt 30 : ℂ))

def sourceContactRow51 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 106
  | 7 => _family 23
  | 8 => _family 22
  | 15 => _family 45
  | 19 => _family 46
  | 20 => _family 47
  | 21 => _family 88
  | 27 => _family 83
  | 31 => _family 84
  | 32 => _family 85
  | 34 => _family 58
  | 39 => _family 98
  | 43 => _family 99
  | 44 => _family 100
  | 51 => _family 107
  | 55 => _family 108
  | 56 => _family 109
  | _ => 0

def pointContactRow51 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow51 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow52 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow52 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow52 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow53 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def contactBraRow54 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow55 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 23
  | 7 => _family 106
  | 8 => _family 23
  | 15 => _family 46
  | 19 => _family 45
  | 20 => _family 46
  | 21 => _family 60
  | 27 => _family 84
  | 31 => _family 83
  | 32 => _family 84
  | 34 => _family 59
  | 39 => _family 99
  | 43 => _family 98
  | 44 => _family 99
  | 51 => _family 108
  | 55 => _family 107
  | 56 => _family 108
  | _ => 0

def pointContactRow55 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow55 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow56 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 4 => _family 22
  | 7 => _family 23
  | 8 => _family 106
  | 15 => _family 47
  | 19 => _family 46
  | 20 => _family 45
  | 21 => _family 59
  | 27 => _family 85
  | 31 => _family 84
  | 32 => _family 83
  | 34 => _family 60
  | 39 => _family 100
  | 43 => _family 99
  | 44 => _family 98
  | 51 => _family 109
  | 55 => _family 108
  | 56 => _family 107
  | _ => 0

def pointContactRow56 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow56 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow57 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow57 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow57 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow58 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow58 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow58 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow59 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow59 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow59 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow60 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow60 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow60 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow61 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow61 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow61 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow62 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow62 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow62 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow63 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow63 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow63 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow64 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow64 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow64 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow65 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow65 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow65 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow66 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow66 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow66 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow67 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow67 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow67 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow68 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow68 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow68 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow69 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow69 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow69 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow70 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow70 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow70 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow71 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow71 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow71 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow72 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def pointContactRow72 (b : Fin 97) : ℂ :=
  match b.val with
  | _ => 0

def contactBraRow72 (dual : Bool) : ℂ :=
  if dual then 0 else 0

def sourceContactRow73 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => _family 111
  | 90 => _family 112
  | 95 => _family 113
  | _ => 0

def pointContactRow73 (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 90 => (1/2)
  | 95 => (-1/2)
  | _ => 0

def contactBraRow73 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow74 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => _family 111
  | 84 => _family 113
  | 94 => _family 112
  | _ => 0

def pointContactRow74 (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 84 => (-1/2)
  | 94 => (1/2)
  | _ => 0

def contactBraRow74 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow75 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => _family 111
  | 83 => _family 112
  | 88 => _family 113
  | _ => 0

def pointContactRow75 (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => ((-3/50) * (Real.sqrt 30 : ℂ))
  | 83 => (1/2)
  | 88 => (-1/2)
  | _ => 0

def contactBraRow75 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow76 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => _family 114
  | 87 => _family 112
  | 92 => _family 113
  | _ => 0

def pointContactRow76 (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => ((3/50) * (Real.sqrt 30 : ℂ))
  | 87 => (1/2)
  | 92 => (-1/2)
  | _ => 0

def contactBraRow76 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow77 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => _family 114
  | 81 => _family 113
  | 91 => _family 112
  | _ => 0

def pointContactRow77 (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => ((3/50) * (Real.sqrt 30 : ℂ))
  | 81 => (-1/2)
  | 91 => (1/2)
  | _ => 0

def contactBraRow77 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow78 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => _family 114
  | 80 => _family 112
  | 85 => _family 113
  | _ => 0

def pointContactRow78 (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => ((3/50) * (Real.sqrt 30 : ℂ))
  | 80 => (1/2)
  | 85 => (-1/2)
  | _ => 0

def contactBraRow78 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow79 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => _family 115
  | 86 => _family 116
  | 93 => _family 116
  | _ => 0

def pointContactRow79 (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 86 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 93 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow79 (dual : Bool) : ℂ :=
  if dual then ((-3/200) * (Real.sqrt 30 : ℂ)) else ((-3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow80 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => _family 112
  | 80 => _family 115
  | 85 => _family 115
  | _ => 0

def pointContactRow80 (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => (1/2)
  | 80 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 85 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow80 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow81 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => _family 113
  | 81 => _family 115
  | 91 => _family 115
  | _ => 0

def pointContactRow81 (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => (-1/2)
  | 81 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 91 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow81 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow82 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => _family 116
  | 89 => _family 115
  | 96 => _family 115
  | _ => 0

def pointContactRow82 (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 89 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 96 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow82 (dual : Bool) : ℂ :=
  if dual then ((1/200) * (Real.sqrt 30 : ℂ)) else ((1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow83 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => _family 112
  | 83 => _family 116
  | 88 => _family 116
  | _ => 0

def pointContactRow83 (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => (1/2)
  | 83 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 88 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow83 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow84 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => _family 113
  | 84 => _family 116
  | 94 => _family 116
  | _ => 0

def pointContactRow84 (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => (-1/2)
  | 84 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 94 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow84 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow85 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => _family 113
  | 80 => _family 115
  | 85 => _family 115
  | _ => 0

def pointContactRow85 (b : Fin 97) : ℂ :=
  match b.val with
  | 78 => (-1/2)
  | 80 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 85 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow85 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow86 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => _family 116
  | 86 => _family 115
  | 93 => _family 116
  | _ => 0

def pointContactRow86 (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 86 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 93 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow86 (dual : Bool) : ℂ :=
  if dual then ((-3/200) * (Real.sqrt 30 : ℂ)) else ((-3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow87 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => _family 112
  | 87 => _family 115
  | 92 => _family 115
  | _ => 0

def pointContactRow87 (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => (1/2)
  | 87 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 92 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow87 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow88 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => _family 113
  | 83 => _family 116
  | 88 => _family 116
  | _ => 0

def pointContactRow88 (b : Fin 97) : ℂ :=
  match b.val with
  | 75 => (-1/2)
  | 83 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 88 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow88 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow89 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => _family 115
  | 89 => _family 116
  | 96 => _family 115
  | _ => 0

def pointContactRow89 (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 89 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 96 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow89 (dual : Bool) : ℂ :=
  if dual then ((1/200) * (Real.sqrt 30 : ℂ)) else ((1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow90 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => _family 112
  | 90 => _family 116
  | 95 => _family 116
  | _ => 0

def pointContactRow90 (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => (1/2)
  | 90 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 95 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow90 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow91 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => _family 112
  | 81 => _family 115
  | 91 => _family 115
  | _ => 0

def pointContactRow91 (b : Fin 97) : ℂ :=
  match b.val with
  | 77 => (1/2)
  | 81 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 91 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow91 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow92 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => _family 113
  | 87 => _family 115
  | 92 => _family 115
  | _ => 0

def pointContactRow92 (b : Fin 97) : ℂ :=
  match b.val with
  | 76 => (-1/2)
  | 87 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 92 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow92 (dual : Bool) : ℂ :=
  if dual then ((-1/200) * (Real.sqrt 30 : ℂ)) else ((-1/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow93 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => _family 116
  | 86 => _family 116
  | 93 => _family 115
  | _ => 0

def pointContactRow93 (b : Fin 97) : ℂ :=
  match b.val with
  | 79 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 86 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 93 => ((5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow93 (dual : Bool) : ℂ :=
  if dual then ((-3/200) * (Real.sqrt 30 : ℂ)) else ((-3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow94 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => _family 112
  | 84 => _family 116
  | 94 => _family 116
  | _ => 0

def pointContactRow94 (b : Fin 97) : ℂ :=
  match b.val with
  | 74 => (1/2)
  | 84 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 94 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow94 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow95 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => _family 113
  | 90 => _family 116
  | 95 => _family 116
  | _ => 0

def pointContactRow95 (b : Fin 97) : ℂ :=
  match b.val with
  | 73 => (-1/2)
  | 90 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | 95 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow95 (dual : Bool) : ℂ :=
  if dual then ((3/200) * (Real.sqrt 30 : ℂ)) else ((3/200) * (Real.sqrt 30 : ℂ))

def sourceContactRow96 (_family : Fin 117 → ℂ) (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => _family 115
  | 89 => _family 115
  | 96 => _family 116
  | _ => 0

def pointContactRow96 (b : Fin 97) : ℂ :=
  match b.val with
  | 82 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 89 => ((5/36) * (Real.sqrt 30 : ℂ))
  | 96 => ((-5/36) * (Real.sqrt 30 : ℂ))
  | _ => 0

def contactBraRow96 (dual : Bool) : ℂ :=
  if dual then ((1/200) * (Real.sqrt 30 : ℂ)) else ((1/200) * (Real.sqrt 30 : ℂ))

end LowEnergy.ActualBraContactDualContraction
