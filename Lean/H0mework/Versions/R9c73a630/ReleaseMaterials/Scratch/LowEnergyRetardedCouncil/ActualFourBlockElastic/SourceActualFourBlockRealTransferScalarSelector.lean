import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferScalarLocal
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer

def scalarNumeratorRow0 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 0 => some 0
  | 5 => some 1
  | _ => none

def scalarNumeratorRow1 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 1 => some 2
  | _ => none

def scalarNumeratorRow2 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 2 => some 2
  | _ => none

def scalarNumeratorRow3 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 3 => some 2
  | _ => none

def scalarNumeratorRow4 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 4 => some 2
  | _ => none

def scalarNumeratorRow5 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 0 => some 1
  | 5 => some 0
  | _ => none

def scalarNumeratorRow6 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 6 => some 2
  | _ => none

def scalarNumeratorRow7 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 7 => some 2
  | _ => none

def scalarNumeratorRow8 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 8 => some 2
  | _ => none

def scalarNumeratorRow9 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 9 => some 2
  | _ => none

def scalarNumeratorRow10 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 10 => some 3
  | 20 => some 4
  | 45 => some 5
  | 55 => some 6
  | _ => none

def scalarNumeratorRow11 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 11 => some 3
  | 21 => some 4
  | 46 => some 5
  | 56 => some 6
  | _ => none

def scalarNumeratorRow12 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 12 => some 3
  | 22 => some 4
  | 47 => some 5
  | 57 => some 6
  | _ => none

def scalarNumeratorRow13 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 7
  | 15 => some 8
  | 23 => some 9
  | 25 => some 10
  | 48 => some 11
  | 50 => some 12
  | 58 => some 13
  | 60 => some 14
  | _ => none

def scalarNumeratorRow14 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 14 => some 3
  | 24 => some 4
  | 49 => some 5
  | 59 => some 6
  | _ => none

def scalarNumeratorRow15 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 8
  | 15 => some 7
  | 23 => some 10
  | 25 => some 9
  | 48 => some 12
  | 50 => some 11
  | 58 => some 14
  | 60 => some 13
  | _ => none

def scalarNumeratorRow16 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 16 => some 3
  | 26 => some 4
  | 51 => some 5
  | 61 => some 6
  | _ => none

def scalarNumeratorRow17 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 17 => some 3
  | 27 => some 4
  | 52 => some 5
  | 62 => some 6
  | _ => none

def scalarNumeratorRow18 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 18 => some 3
  | 28 => some 4
  | 53 => some 5
  | 63 => some 6
  | _ => none

def scalarNumeratorRow19 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 19 => some 3
  | 29 => some 4
  | 54 => some 5
  | 64 => some 6
  | _ => none

def scalarNumeratorRow20 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 10 => some 15
  | 20 => some 3
  | 45 => some 6
  | 55 => some 16
  | _ => none

def scalarNumeratorRow21 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 11 => some 15
  | 21 => some 3
  | 46 => some 6
  | 56 => some 16
  | _ => none

def scalarNumeratorRow22 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 12 => some 15
  | 22 => some 3
  | 47 => some 6
  | 57 => some 16
  | _ => none

def scalarNumeratorRow23 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 10
  | 15 => some 9
  | 23 => some 7
  | 25 => some 8
  | 48 => some 13
  | 50 => some 14
  | 58 => some 12
  | 60 => some 11
  | _ => none

def scalarNumeratorRow24 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 14 => some 15
  | 24 => some 3
  | 49 => some 6
  | 59 => some 16
  | _ => none

def scalarNumeratorRow25 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 9
  | 15 => some 10
  | 23 => some 8
  | 25 => some 7
  | 48 => some 14
  | 50 => some 13
  | 58 => some 11
  | 60 => some 12
  | _ => none

def scalarNumeratorRow26 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 16 => some 15
  | 26 => some 3
  | 51 => some 6
  | 61 => some 16
  | _ => none

def scalarNumeratorRow27 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 17 => some 15
  | 27 => some 3
  | 52 => some 6
  | 62 => some 16
  | _ => none

def scalarNumeratorRow28 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 18 => some 15
  | 28 => some 3
  | 53 => some 6
  | 63 => some 16
  | _ => none

def scalarNumeratorRow29 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 19 => some 15
  | 29 => some 3
  | 54 => some 6
  | 64 => some 16
  | _ => none

def scalarNumeratorRow30 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 30 => some 2
  | _ => none

def scalarNumeratorRow31 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 31 => some 2
  | _ => none

def scalarNumeratorRow32 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 32 => some 2
  | _ => none

def scalarNumeratorRow33 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 33 => some 2
  | _ => none

def scalarNumeratorRow34 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 34 => some 2
  | _ => none

def scalarNumeratorRow35 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 35 => some 0
  | 40 => some 1
  | _ => none

def scalarNumeratorRow36 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 36 => some 17
  | 38 => some 18
  | 42 => some 18
  | 44 => some 17
  | _ => none

def scalarNumeratorRow37 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 37 => some 2
  | _ => none

def scalarNumeratorRow38 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 36 => some 18
  | 38 => some 17
  | 42 => some 17
  | 44 => some 18
  | _ => none

def scalarNumeratorRow39 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 39 => some 2
  | _ => none

def scalarNumeratorRow40 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 35 => some 1
  | 40 => some 0
  | _ => none

def scalarNumeratorRow41 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 41 => some 2
  | _ => none

def scalarNumeratorRow42 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 36 => some 18
  | 38 => some 17
  | 42 => some 17
  | 44 => some 18
  | _ => none

def scalarNumeratorRow43 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 43 => some 2
  | _ => none

def scalarNumeratorRow44 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 36 => some 17
  | 38 => some 18
  | 42 => some 18
  | 44 => some 17
  | _ => none

def scalarNumeratorRow45 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 10 => some 16
  | 20 => some 19
  | 45 => some 3
  | 55 => some 4
  | _ => none

def scalarNumeratorRow46 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 11 => some 16
  | 21 => some 19
  | 46 => some 3
  | 56 => some 4
  | _ => none

def scalarNumeratorRow47 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 12 => some 16
  | 22 => some 19
  | 47 => some 3
  | 57 => some 4
  | _ => none

def scalarNumeratorRow48 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 12
  | 15 => some 11
  | 23 => some 14
  | 25 => some 13
  | 48 => some 7
  | 50 => some 8
  | 58 => some 9
  | 60 => some 10
  | _ => none

def scalarNumeratorRow49 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 14 => some 16
  | 24 => some 19
  | 49 => some 3
  | 59 => some 4
  | _ => none

def scalarNumeratorRow50 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 11
  | 15 => some 12
  | 23 => some 13
  | 25 => some 14
  | 48 => some 8
  | 50 => some 7
  | 58 => some 10
  | 60 => some 9
  | _ => none

def scalarNumeratorRow51 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 16 => some 16
  | 26 => some 19
  | 51 => some 3
  | 61 => some 4
  | _ => none

def scalarNumeratorRow52 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 17 => some 16
  | 27 => some 19
  | 52 => some 3
  | 62 => some 4
  | _ => none

def scalarNumeratorRow53 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 18 => some 16
  | 28 => some 19
  | 53 => some 3
  | 63 => some 4
  | _ => none

def scalarNumeratorRow54 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 19 => some 16
  | 29 => some 19
  | 54 => some 3
  | 64 => some 4
  | _ => none

def scalarNumeratorRow55 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 10 => some 19
  | 20 => some 5
  | 45 => some 15
  | 55 => some 3
  | _ => none

def scalarNumeratorRow56 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 11 => some 19
  | 21 => some 5
  | 46 => some 15
  | 56 => some 3
  | _ => none

def scalarNumeratorRow57 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 12 => some 19
  | 22 => some 5
  | 47 => some 15
  | 57 => some 3
  | _ => none

def scalarNumeratorRow58 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 14
  | 15 => some 13
  | 23 => some 11
  | 25 => some 12
  | 48 => some 10
  | 50 => some 9
  | 58 => some 7
  | 60 => some 8
  | _ => none

def scalarNumeratorRow59 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 14 => some 19
  | 24 => some 5
  | 49 => some 15
  | 59 => some 3
  | _ => none

def scalarNumeratorRow60 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 13 => some 13
  | 15 => some 14
  | 23 => some 12
  | 25 => some 11
  | 48 => some 9
  | 50 => some 10
  | 58 => some 8
  | 60 => some 7
  | _ => none

def scalarNumeratorRow61 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 16 => some 19
  | 26 => some 5
  | 51 => some 15
  | 61 => some 3
  | _ => none

def scalarNumeratorRow62 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 17 => some 19
  | 27 => some 5
  | 52 => some 15
  | 62 => some 3
  | _ => none

def scalarNumeratorRow63 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 18 => some 19
  | 28 => some 5
  | 53 => some 15
  | 63 => some 3
  | _ => none

def scalarNumeratorRow64 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 19 => some 19
  | 29 => some 5
  | 54 => some 15
  | 64 => some 3
  | _ => none

def scalarNumeratorRow65 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 65 => some 2
  | _ => none

def scalarNumeratorRow66 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 66 => some 2
  | _ => none

def scalarNumeratorRow67 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 67 => some 2
  | _ => none

def scalarNumeratorRow68 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 68 => some 2
  | _ => none

def scalarNumeratorRow69 (b : Fin 70) : Option (Fin 20) :=
  match b.val with
  | 69 => some 2
  | _ => none

def scalarNumeratorIndex (a b : Fin 70) : Option (Fin 20) :=
  match a.val with
  | 0 => scalarNumeratorRow0 b
  | 1 => scalarNumeratorRow1 b
  | 2 => scalarNumeratorRow2 b
  | 3 => scalarNumeratorRow3 b
  | 4 => scalarNumeratorRow4 b
  | 5 => scalarNumeratorRow5 b
  | 6 => scalarNumeratorRow6 b
  | 7 => scalarNumeratorRow7 b
  | 8 => scalarNumeratorRow8 b
  | 9 => scalarNumeratorRow9 b
  | 10 => scalarNumeratorRow10 b
  | 11 => scalarNumeratorRow11 b
  | 12 => scalarNumeratorRow12 b
  | 13 => scalarNumeratorRow13 b
  | 14 => scalarNumeratorRow14 b
  | 15 => scalarNumeratorRow15 b
  | 16 => scalarNumeratorRow16 b
  | 17 => scalarNumeratorRow17 b
  | 18 => scalarNumeratorRow18 b
  | 19 => scalarNumeratorRow19 b
  | 20 => scalarNumeratorRow20 b
  | 21 => scalarNumeratorRow21 b
  | 22 => scalarNumeratorRow22 b
  | 23 => scalarNumeratorRow23 b
  | 24 => scalarNumeratorRow24 b
  | 25 => scalarNumeratorRow25 b
  | 26 => scalarNumeratorRow26 b
  | 27 => scalarNumeratorRow27 b
  | 28 => scalarNumeratorRow28 b
  | 29 => scalarNumeratorRow29 b
  | 30 => scalarNumeratorRow30 b
  | 31 => scalarNumeratorRow31 b
  | 32 => scalarNumeratorRow32 b
  | 33 => scalarNumeratorRow33 b
  | 34 => scalarNumeratorRow34 b
  | 35 => scalarNumeratorRow35 b
  | 36 => scalarNumeratorRow36 b
  | 37 => scalarNumeratorRow37 b
  | 38 => scalarNumeratorRow38 b
  | 39 => scalarNumeratorRow39 b
  | 40 => scalarNumeratorRow40 b
  | 41 => scalarNumeratorRow41 b
  | 42 => scalarNumeratorRow42 b
  | 43 => scalarNumeratorRow43 b
  | 44 => scalarNumeratorRow44 b
  | 45 => scalarNumeratorRow45 b
  | 46 => scalarNumeratorRow46 b
  | 47 => scalarNumeratorRow47 b
  | 48 => scalarNumeratorRow48 b
  | 49 => scalarNumeratorRow49 b
  | 50 => scalarNumeratorRow50 b
  | 51 => scalarNumeratorRow51 b
  | 52 => scalarNumeratorRow52 b
  | 53 => scalarNumeratorRow53 b
  | 54 => scalarNumeratorRow54 b
  | 55 => scalarNumeratorRow55 b
  | 56 => scalarNumeratorRow56 b
  | 57 => scalarNumeratorRow57 b
  | 58 => scalarNumeratorRow58 b
  | 59 => scalarNumeratorRow59 b
  | 60 => scalarNumeratorRow60 b
  | 61 => scalarNumeratorRow61 b
  | 62 => scalarNumeratorRow62 b
  | 63 => scalarNumeratorRow63 b
  | 64 => scalarNumeratorRow64 b
  | 65 => scalarNumeratorRow65 b
  | 66 => scalarNumeratorRow66 b
  | 67 => scalarNumeratorRow67 b
  | 68 => scalarNumeratorRow68 b
  | 69 => scalarNumeratorRow69 b
  | _ => none

def scalarNumeratorRead (p : Fin 4 → ℂ) (a b : Fin 70) : ℂ :=
  match scalarNumeratorIndex a b with
  | none => 0
  | some i => MixedSpectatorScalar61Exchange.numeratorPolynomial p i

end LowEnergy.ActualFourBlockRealTransfer
