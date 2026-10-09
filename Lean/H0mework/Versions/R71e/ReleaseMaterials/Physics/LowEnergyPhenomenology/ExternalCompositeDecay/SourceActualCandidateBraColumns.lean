import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraLeftData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexLiterals
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open ActualCandidateVertexEntries

def column0 (a : Fin 97) : ℂ :=
  match a.val with
  | 15 => ActualCandidateVertexLiterals.coefficient 2
  | 20 => ActualCandidateVertexLiterals.coefficient 2
  | 51 => ActualCandidateVertexLiterals.coefficient 6
  | 56 => ActualCandidateVertexLiterals.coefficient 6
  | 57 => ActualCandidateVertexLiterals.coefficient 8
  | 60 => ActualCandidateVertexLiterals.coefficient 16
  | 62 => ActualCandidateVertexLiterals.coefficient 22
  | 63 => ActualCandidateVertexLiterals.coefficient 30
  | 66 => ActualCandidateVertexLiterals.coefficient 33
  | 67 => ActualCandidateVertexLiterals.coefficient 22
  | 69 => ActualCandidateVertexLiterals.coefficient 40
  | 72 => ActualCandidateVertexLiterals.coefficient 26
  | 75 => ActualCandidateVertexLiterals.coefficient 53
  | 78 => ActualCandidateVertexLiterals.coefficient 56
  | 79 => ActualCandidateVertexLiterals.coefficient 57
  | 80 => ActualCandidateVertexLiterals.coefficient 58
  | 82 => ActualCandidateVertexLiterals.coefficient 58
  | 83 => ActualCandidateVertexLiterals.coefficient 60
  | 85 => ActualCandidateVertexLiterals.coefficient 59
  | 86 => ActualCandidateVertexLiterals.coefficient 57
  | 88 => ActualCandidateVertexLiterals.coefficient 57
  | 89 => ActualCandidateVertexLiterals.coefficient 58
  | 93 => ActualCandidateVertexLiterals.coefficient 57
  | 96 => ActualCandidateVertexLiterals.coefficient 58
  | _ => 0

theorem actual_column0 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 0 0 0 = column0 a := by
  fin_cases a <;> rfl

def column1 (a : Fin 97) : ℂ :=
  match a.val with
  | 9 => ActualCandidateVertexLiterals.coefficient 0
  | 10 => ActualCandidateVertexLiterals.coefficient 2
  | 45 => ActualCandidateVertexLiterals.coefficient 4
  | 46 => ActualCandidateVertexLiterals.coefficient 6
  | 61 => ActualCandidateVertexLiterals.coefficient 20
  | 64 => ActualCandidateVertexLiterals.coefficient 23
  | 65 => ActualCandidateVertexLiterals.coefficient 36
  | 68 => ActualCandidateVertexLiterals.coefficient 31
  | _ => 0

theorem actual_column1 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 0 0 1 = column1 a := by
  fin_cases a <;> rfl

def column2 (a : Fin 97) : ℂ :=
  match a.val with
  | 11 => ActualCandidateVertexLiterals.coefficient 0
  | 12 => ActualCandidateVertexLiterals.coefficient 2
  | 47 => ActualCandidateVertexLiterals.coefficient 4
  | 48 => ActualCandidateVertexLiterals.coefficient 6
  | _ => 0

theorem actual_column2 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 0 0 2 = column2 a := by
  fin_cases a <;> rfl

def column3 (a : Fin 97) : ℂ :=
  match a.val with
  | 27 => ActualCandidateVertexLiterals.coefficient 6
  | 32 => ActualCandidateVertexLiterals.coefficient 6
  | 39 => ActualCandidateVertexLiterals.coefficient 4
  | 44 => ActualCandidateVertexLiterals.coefficient 4
  | 58 => ActualCandidateVertexLiterals.coefficient 16
  | 59 => ActualCandidateVertexLiterals.coefficient 17
  | 61 => ActualCandidateVertexLiterals.coefficient 21
  | 64 => ActualCandidateVertexLiterals.coefficient 34
  | 65 => ActualCandidateVertexLiterals.coefficient 37
  | 68 => ActualCandidateVertexLiterals.coefficient 30
  | 70 => ActualCandidateVertexLiterals.coefficient 45
  | 71 => ActualCandidateVertexLiterals.coefficient 49
  | 73 => ActualCandidateVertexLiterals.coefficient 53
  | 74 => ActualCandidateVertexLiterals.coefficient 55
  | 76 => ActualCandidateVertexLiterals.coefficient 56
  | 77 => ActualCandidateVertexLiterals.coefficient 53
  | 81 => ActualCandidateVertexLiterals.coefficient 60
  | 84 => ActualCandidateVertexLiterals.coefficient 59
  | 87 => ActualCandidateVertexLiterals.coefficient 58
  | 90 => ActualCandidateVertexLiterals.coefficient 60
  | 91 => ActualCandidateVertexLiterals.coefficient 57
  | 92 => ActualCandidateVertexLiterals.coefficient 59
  | 94 => ActualCandidateVertexLiterals.coefficient 58
  | 95 => ActualCandidateVertexLiterals.coefficient 57
  | _ => 0

theorem actual_column3 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 1 0 0 = column3 a := by
  fin_cases a <;> rfl

def column4 (a : Fin 97) : ℂ :=
  match a.val with
  | 21 => ActualCandidateVertexLiterals.coefficient 4
  | 22 => ActualCandidateVertexLiterals.coefficient 6
  | 33 => ActualCandidateVertexLiterals.coefficient 7
  | 34 => ActualCandidateVertexLiterals.coefficient 4
  | 62 => ActualCandidateVertexLiterals.coefficient 23
  | 63 => ActualCandidateVertexLiterals.coefficient 31
  | 66 => ActualCandidateVertexLiterals.coefficient 31
  | 67 => ActualCandidateVertexLiterals.coefficient 25
  | _ => 0

theorem actual_column4 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 1 0 1 = column4 a := by
  fin_cases a <;> rfl

def column5 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column5 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 2 0 0 = column5 a := by
  fin_cases a <;> rfl

def column6 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column6 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 0 2 0 2 = column6 a := by
  fin_cases a <;> rfl

def column7 (a : Fin 97) : ℂ :=
  match a.val with
  | 21 => ActualCandidateVertexLiterals.coefficient 5
  | 22 => ActualCandidateVertexLiterals.coefficient 6
  | 33 => ActualCandidateVertexLiterals.coefficient 7
  | 34 => ActualCandidateVertexLiterals.coefficient 5
  | 62 => ActualCandidateVertexLiterals.coefficient 23
  | 63 => ActualCandidateVertexLiterals.coefficient 32
  | 66 => ActualCandidateVertexLiterals.coefficient 32
  | 67 => ActualCandidateVertexLiterals.coefficient 25
  | _ => 0

theorem actual_column7 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 0 1 0 = column7 a := by
  fin_cases a <;> rfl

def column8 (a : Fin 97) : ℂ :=
  match a.val with
  | 28 => ActualCandidateVertexLiterals.coefficient 6
  | 32 => ActualCandidateVertexLiterals.coefficient 6
  | 40 => ActualCandidateVertexLiterals.coefficient 5
  | 44 => ActualCandidateVertexLiterals.coefficient 5
  | 58 => ActualCandidateVertexLiterals.coefficient 16
  | 59 => ActualCandidateVertexLiterals.coefficient 18
  | 61 => ActualCandidateVertexLiterals.coefficient 21
  | 64 => ActualCandidateVertexLiterals.coefficient 35
  | 65 => ActualCandidateVertexLiterals.coefficient 39
  | 68 => ActualCandidateVertexLiterals.coefficient 30
  | 70 => ActualCandidateVertexLiterals.coefficient 48
  | 71 => ActualCandidateVertexLiterals.coefficient 49
  | 73 => ActualCandidateVertexLiterals.coefficient 53
  | 74 => ActualCandidateVertexLiterals.coefficient 56
  | 76 => ActualCandidateVertexLiterals.coefficient 56
  | 77 => ActualCandidateVertexLiterals.coefficient 54
  | 81 => ActualCandidateVertexLiterals.coefficient 57
  | 84 => ActualCandidateVertexLiterals.coefficient 58
  | 87 => ActualCandidateVertexLiterals.coefficient 58
  | 90 => ActualCandidateVertexLiterals.coefficient 60
  | 91 => ActualCandidateVertexLiterals.coefficient 60
  | 92 => ActualCandidateVertexLiterals.coefficient 59
  | 94 => ActualCandidateVertexLiterals.coefficient 59
  | 95 => ActualCandidateVertexLiterals.coefficient 57
  | _ => 0

theorem actual_column8 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 0 1 1 = column8 a := by
  fin_cases a <;> rfl

def column9 (a : Fin 97) : ℂ :=
  match a.val with
  | 25 => ActualCandidateVertexLiterals.coefficient 4
  | 26 => ActualCandidateVertexLiterals.coefficient 6
  | 37 => ActualCandidateVertexLiterals.coefficient 6
  | 38 => ActualCandidateVertexLiterals.coefficient 5
  | _ => 0

theorem actual_column9 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 0 1 2 = column9 a := by
  fin_cases a <;> rfl

def column10 (a : Fin 97) : ℂ :=
  match a.val with
  | 9 => ActualCandidateVertexLiterals.coefficient 1
  | 10 => ActualCandidateVertexLiterals.coefficient 2
  | 45 => ActualCandidateVertexLiterals.coefficient 4
  | 46 => ActualCandidateVertexLiterals.coefficient 7
  | 61 => ActualCandidateVertexLiterals.coefficient 20
  | 64 => ActualCandidateVertexLiterals.coefficient 25
  | 65 => ActualCandidateVertexLiterals.coefficient 38
  | 68 => ActualCandidateVertexLiterals.coefficient 31
  | _ => 0

theorem actual_column10 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 1 1 0 = column10 a := by
  fin_cases a <;> rfl

def column11 (a : Fin 97) : ℂ :=
  match a.val with
  | 16 => ActualCandidateVertexLiterals.coefficient 2
  | 20 => ActualCandidateVertexLiterals.coefficient 2
  | 52 => ActualCandidateVertexLiterals.coefficient 7
  | 56 => ActualCandidateVertexLiterals.coefficient 7
  | 57 => ActualCandidateVertexLiterals.coefficient 8
  | 60 => ActualCandidateVertexLiterals.coefficient 19
  | 62 => ActualCandidateVertexLiterals.coefficient 22
  | 63 => ActualCandidateVertexLiterals.coefficient 33
  | 66 => ActualCandidateVertexLiterals.coefficient 30
  | 67 => ActualCandidateVertexLiterals.coefficient 22
  | 69 => ActualCandidateVertexLiterals.coefficient 43
  | 72 => ActualCandidateVertexLiterals.coefficient 26
  | 75 => ActualCandidateVertexLiterals.coefficient 54
  | 78 => ActualCandidateVertexLiterals.coefficient 55
  | 79 => ActualCandidateVertexLiterals.coefficient 57
  | 80 => ActualCandidateVertexLiterals.coefficient 59
  | 82 => ActualCandidateVertexLiterals.coefficient 58
  | 83 => ActualCandidateVertexLiterals.coefficient 57
  | 85 => ActualCandidateVertexLiterals.coefficient 58
  | 86 => ActualCandidateVertexLiterals.coefficient 57
  | 88 => ActualCandidateVertexLiterals.coefficient 60
  | 89 => ActualCandidateVertexLiterals.coefficient 58
  | 93 => ActualCandidateVertexLiterals.coefficient 57
  | 96 => ActualCandidateVertexLiterals.coefficient 58
  | _ => 0

theorem actual_column11 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 1 1 1 = column11 a := by
  fin_cases a <;> rfl

def column12 (a : Fin 97) : ℂ :=
  match a.val with
  | 13 => ActualCandidateVertexLiterals.coefficient 0
  | 14 => ActualCandidateVertexLiterals.coefficient 2
  | 49 => ActualCandidateVertexLiterals.coefficient 5
  | 50 => ActualCandidateVertexLiterals.coefficient 7
  | _ => 0

theorem actual_column12 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 1 1 2 = column12 a := by
  fin_cases a <;> rfl

def column13 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column13 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 2 1 1 = column13 a := by
  fin_cases a <;> rfl

def column14 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column14 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 2 1 2 = column14 a := by
  fin_cases a <;> rfl

def column15 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column15 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 3 1 1 = column15 a := by
  fin_cases a <;> rfl

def column16 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column16 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 1 3 1 2 = column16 a := by
  fin_cases a <;> rfl

def column17 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column17 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 0 2 0 = column17 a := by
  fin_cases a <;> rfl

def column18 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column18 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 0 2 1 = column18 a := by
  fin_cases a <;> rfl

def column19 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column19 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 0 2 2 = column19 a := by
  fin_cases a <;> rfl

def column20 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column20 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 1 2 1 = column20 a := by
  fin_cases a <;> rfl

def column21 (a : Fin 97) : ℂ :=
  match a.val with
  | _ => 0

theorem actual_column21 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 1 2 2 = column21 a := by
  fin_cases a <;> rfl

def column22 (a : Fin 97) : ℂ :=
  match a.val with
  | 11 => ActualCandidateVertexLiterals.coefficient 1
  | 12 => ActualCandidateVertexLiterals.coefficient 2
  | 47 => ActualCandidateVertexLiterals.coefficient 4
  | 48 => ActualCandidateVertexLiterals.coefficient 7
  | _ => 0

theorem actual_column22 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 2 2 0 = column22 a := by
  fin_cases a <;> rfl

def column23 (a : Fin 97) : ℂ :=
  match a.val with
  | 13 => ActualCandidateVertexLiterals.coefficient 1
  | 14 => ActualCandidateVertexLiterals.coefficient 2
  | 49 => ActualCandidateVertexLiterals.coefficient 4
  | 50 => ActualCandidateVertexLiterals.coefficient 7
  | _ => 0

theorem actual_column23 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 2 2 1 = column23 a := by
  fin_cases a <;> rfl

def column24 (a : Fin 97) : ℂ :=
  match a.val with
  | 15 => ActualCandidateVertexLiterals.coefficient 3
  | 16 => ActualCandidateVertexLiterals.coefficient 3
  | 19 => ActualCandidateVertexLiterals.coefficient 2
  | 51 => ActualCandidateVertexLiterals.coefficient 6
  | 52 => ActualCandidateVertexLiterals.coefficient 6
  | 55 => ActualCandidateVertexLiterals.coefficient 7
  | 57 => ActualCandidateVertexLiterals.coefficient 15
  | 60 => ActualCandidateVertexLiterals.coefficient 16
  | 62 => ActualCandidateVertexLiterals.coefficient 29
  | 63 => ActualCandidateVertexLiterals.coefficient 33
  | 66 => ActualCandidateVertexLiterals.coefficient 30
  | 67 => ActualCandidateVertexLiterals.coefficient 29
  | 69 => ActualCandidateVertexLiterals.coefficient 21
  | 72 => ActualCandidateVertexLiterals.coefficient 29
  | 75 => ActualCandidateVertexLiterals.coefficient 54
  | 78 => ActualCandidateVertexLiterals.coefficient 56
  | 79 => ActualCandidateVertexLiterals.coefficient 57
  | 80 => ActualCandidateVertexLiterals.coefficient 58
  | 82 => ActualCandidateVertexLiterals.coefficient 59
  | 83 => ActualCandidateVertexLiterals.coefficient 57
  | 85 => ActualCandidateVertexLiterals.coefficient 59
  | 86 => ActualCandidateVertexLiterals.coefficient 57
  | 88 => ActualCandidateVertexLiterals.coefficient 60
  | 89 => ActualCandidateVertexLiterals.coefficient 59
  | 93 => ActualCandidateVertexLiterals.coefficient 57
  | 96 => ActualCandidateVertexLiterals.coefficient 59
  | _ => 0

theorem actual_column24 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 2 2 2 = column24 a := by
  fin_cases a <;> rfl

def column25 (a : Fin 97) : ℂ :=
  match a.val with
  | 25 => ActualCandidateVertexLiterals.coefficient 4
  | 26 => ActualCandidateVertexLiterals.coefficient 7
  | 37 => ActualCandidateVertexLiterals.coefficient 7
  | 38 => ActualCandidateVertexLiterals.coefficient 5
  | _ => 0

theorem actual_column25 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 3 2 1 = column25 a := by
  fin_cases a <;> rfl

def column26 (a : Fin 97) : ℂ :=
  match a.val with
  | 27 => ActualCandidateVertexLiterals.coefficient 6
  | 28 => ActualCandidateVertexLiterals.coefficient 6
  | 31 => ActualCandidateVertexLiterals.coefficient 7
  | 39 => ActualCandidateVertexLiterals.coefficient 4
  | 40 => ActualCandidateVertexLiterals.coefficient 4
  | 43 => ActualCandidateVertexLiterals.coefficient 5
  | 58 => ActualCandidateVertexLiterals.coefficient 16
  | 59 => ActualCandidateVertexLiterals.coefficient 17
  | 61 => ActualCandidateVertexLiterals.coefficient 21
  | 64 => ActualCandidateVertexLiterals.coefficient 35
  | 65 => ActualCandidateVertexLiterals.coefficient 37
  | 68 => ActualCandidateVertexLiterals.coefficient 33
  | 70 => ActualCandidateVertexLiterals.coefficient 34
  | 71 => ActualCandidateVertexLiterals.coefficient 30
  | 73 => ActualCandidateVertexLiterals.coefficient 54
  | 74 => ActualCandidateVertexLiterals.coefficient 56
  | 76 => ActualCandidateVertexLiterals.coefficient 56
  | 77 => ActualCandidateVertexLiterals.coefficient 53
  | 81 => ActualCandidateVertexLiterals.coefficient 60
  | 84 => ActualCandidateVertexLiterals.coefficient 58
  | 87 => ActualCandidateVertexLiterals.coefficient 58
  | 90 => ActualCandidateVertexLiterals.coefficient 57
  | 91 => ActualCandidateVertexLiterals.coefficient 57
  | 92 => ActualCandidateVertexLiterals.coefficient 59
  | 94 => ActualCandidateVertexLiterals.coefficient 59
  | 95 => ActualCandidateVertexLiterals.coefficient 60
  | _ => 0

theorem actual_column26 (a : Fin 97) :
    ActualCandidateVertexLiterals.primalLiteral a 2 3 2 2 = column26 a := by
  fin_cases a <;> rfl

end LowEnergy.ActualCandidateBra
