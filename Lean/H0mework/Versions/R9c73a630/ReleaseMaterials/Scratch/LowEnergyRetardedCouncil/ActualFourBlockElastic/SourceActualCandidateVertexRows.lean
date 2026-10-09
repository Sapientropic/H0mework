import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexRowAliases
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexValuesCoframe
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open ActualCandidateVertexEntries

def vertexRow (a : Fin 97) (s t : Fin 4) (c d : Fin 3) : ℂ :=
  match a.val with
  | 9 => (source_vertex_row% 9) s t c d
  | 10 => (source_vertex_row% 10) s t c d
  | 11 => (source_vertex_row% 11) s t c d
  | 12 => (source_vertex_row% 12) s t c d
  | 13 => (source_vertex_row% 13) s t c d
  | 14 => (source_vertex_row% 14) s t c d
  | 15 => (source_vertex_row% 15) s t c d
  | 16 => (source_vertex_row% 16) s t c d
  | 17 => (source_vertex_row% 17) s t c d
  | 18 => (source_vertex_row% 18) s t c d
  | 19 => (source_vertex_row% 19) s t c d
  | 20 => (source_vertex_row% 20) s t c d
  | 21 => (source_vertex_row% 21) s t c d
  | 22 => (source_vertex_row% 22) s t c d
  | 23 => (source_vertex_row% 23) s t c d
  | 24 => (source_vertex_row% 24) s t c d
  | 25 => (source_vertex_row% 25) s t c d
  | 26 => (source_vertex_row% 26) s t c d
  | 27 => (source_vertex_row% 27) s t c d
  | 28 => (source_vertex_row% 28) s t c d
  | 29 => (source_vertex_row% 29) s t c d
  | 30 => (source_vertex_row% 30) s t c d
  | 31 => (source_vertex_row% 31) s t c d
  | 32 => (source_vertex_row% 32) s t c d
  | 33 => (source_vertex_row% 33) s t c d
  | 34 => (source_vertex_row% 34) s t c d
  | 35 => (source_vertex_row% 35) s t c d
  | 36 => (source_vertex_row% 36) s t c d
  | 37 => (source_vertex_row% 37) s t c d
  | 38 => (source_vertex_row% 38) s t c d
  | 39 => (source_vertex_row% 39) s t c d
  | 40 => (source_vertex_row% 40) s t c d
  | 41 => (source_vertex_row% 41) s t c d
  | 42 => (source_vertex_row% 42) s t c d
  | 43 => (source_vertex_row% 43) s t c d
  | 44 => (source_vertex_row% 44) s t c d
  | 45 => (source_vertex_row% 45) s t c d
  | 46 => (source_vertex_row% 46) s t c d
  | 47 => (source_vertex_row% 47) s t c d
  | 48 => (source_vertex_row% 48) s t c d
  | 49 => (source_vertex_row% 49) s t c d
  | 50 => (source_vertex_row% 50) s t c d
  | 51 => (source_vertex_row% 51) s t c d
  | 52 => (source_vertex_row% 52) s t c d
  | 53 => (source_vertex_row% 53) s t c d
  | 54 => (source_vertex_row% 54) s t c d
  | 55 => (source_vertex_row% 55) s t c d
  | 56 => (source_vertex_row% 56) s t c d
  | 57 => (source_vertex_row% 57) s t c d
  | 58 => (source_vertex_row% 58) s t c d
  | 59 => (source_vertex_row% 59) s t c d
  | 60 => (source_vertex_row% 60) s t c d
  | 61 => (source_vertex_row% 61) s t c d
  | 62 => (source_vertex_row% 62) s t c d
  | 63 => (source_vertex_row% 63) s t c d
  | 64 => (source_vertex_row% 64) s t c d
  | 65 => (source_vertex_row% 65) s t c d
  | 66 => (source_vertex_row% 66) s t c d
  | 67 => (source_vertex_row% 67) s t c d
  | 68 => (source_vertex_row% 68) s t c d
  | 69 => (source_vertex_row% 69) s t c d
  | 70 => (source_vertex_row% 70) s t c d
  | 71 => (source_vertex_row% 71) s t c d
  | 72 => (source_vertex_row% 72) s t c d
  | 73 => (source_vertex_row% 73) s t c d
  | 74 => (source_vertex_row% 74) s t c d
  | 75 => (source_vertex_row% 75) s t c d
  | 76 => (source_vertex_row% 76) s t c d
  | 77 => (source_vertex_row% 77) s t c d
  | 78 => (source_vertex_row% 78) s t c d
  | 79 => (source_vertex_row% 79) s t c d
  | 80 => (source_vertex_row% 80) s t c d
  | 81 => (source_vertex_row% 81) s t c d
  | 82 => (source_vertex_row% 82) s t c d
  | 83 => (source_vertex_row% 83) s t c d
  | 84 => (source_vertex_row% 84) s t c d
  | 85 => (source_vertex_row% 85) s t c d
  | 86 => (source_vertex_row% 86) s t c d
  | 87 => (source_vertex_row% 87) s t c d
  | 88 => (source_vertex_row% 88) s t c d
  | 89 => (source_vertex_row% 89) s t c d
  | 90 => (source_vertex_row% 90) s t c d
  | 91 => (source_vertex_row% 91) s t c d
  | 92 => (source_vertex_row% 92) s t c d
  | 93 => (source_vertex_row% 93) s t c d
  | 94 => (source_vertex_row% 94) s t c d
  | 95 => (source_vertex_row% 95) s t c d
  | 96 => (source_vertex_row% 96) s t c d
  | _ => 0

def entryMatrix (a : Fin 97) : Matrix Support Support ℂ :=
  fun i j => vertexRow a i.1 j.1 i.2 j.2

theorem actual_primal_row (a : Fin 97) (s t : Fin 4) (c d : Fin 3) :
    ActualCandidateVertexLiterals.primalLiteral a s t c d = vertexRow a s t c d := by
  fin_cases a
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (source_vertex_row_original% 9) s t c d
  · exact (source_vertex_row_original% 10) s t c d
  · exact (source_vertex_row_original% 11) s t c d
  · exact (source_vertex_row_original% 12) s t c d
  · exact (source_vertex_row_original% 13) s t c d
  · exact (source_vertex_row_original% 14) s t c d
  · exact (source_vertex_row_original% 15) s t c d
  · exact (source_vertex_row_original% 16) s t c d
  · exact (source_vertex_row_original% 17) s t c d
  · exact (source_vertex_row_original% 18) s t c d
  · exact (source_vertex_row_original% 19) s t c d
  · exact (source_vertex_row_original% 20) s t c d
  · exact (source_vertex_row_original% 21) s t c d
  · exact (source_vertex_row_original% 22) s t c d
  · exact (source_vertex_row_original% 23) s t c d
  · exact (source_vertex_row_original% 24) s t c d
  · exact (source_vertex_row_original% 25) s t c d
  · exact (source_vertex_row_original% 26) s t c d
  · exact (source_vertex_row_original% 27) s t c d
  · exact (source_vertex_row_original% 28) s t c d
  · exact (source_vertex_row_original% 29) s t c d
  · exact (source_vertex_row_original% 30) s t c d
  · exact (source_vertex_row_original% 31) s t c d
  · exact (source_vertex_row_original% 32) s t c d
  · exact (source_vertex_row_original% 33) s t c d
  · exact (source_vertex_row_original% 34) s t c d
  · exact (source_vertex_row_original% 35) s t c d
  · exact (source_vertex_row_original% 36) s t c d
  · exact (source_vertex_row_original% 37) s t c d
  · exact (source_vertex_row_original% 38) s t c d
  · exact (source_vertex_row_original% 39) s t c d
  · exact (source_vertex_row_original% 40) s t c d
  · exact (source_vertex_row_original% 41) s t c d
  · exact (source_vertex_row_original% 42) s t c d
  · exact (source_vertex_row_original% 43) s t c d
  · exact (source_vertex_row_original% 44) s t c d
  · exact (source_vertex_row_original% 45) s t c d
  · exact (source_vertex_row_original% 46) s t c d
  · exact (source_vertex_row_original% 47) s t c d
  · exact (source_vertex_row_original% 48) s t c d
  · exact (source_vertex_row_original% 49) s t c d
  · exact (source_vertex_row_original% 50) s t c d
  · exact (source_vertex_row_original% 51) s t c d
  · exact (source_vertex_row_original% 52) s t c d
  · exact (source_vertex_row_original% 53) s t c d
  · exact (source_vertex_row_original% 54) s t c d
  · exact (source_vertex_row_original% 55) s t c d
  · exact (source_vertex_row_original% 56) s t c d
  · exact (source_vertex_row_original% 57) s t c d
  · exact (source_vertex_row_original% 58) s t c d
  · exact (source_vertex_row_original% 59) s t c d
  · exact (source_vertex_row_original% 60) s t c d
  · exact (source_vertex_row_original% 61) s t c d
  · exact (source_vertex_row_original% 62) s t c d
  · exact (source_vertex_row_original% 63) s t c d
  · exact (source_vertex_row_original% 64) s t c d
  · exact (source_vertex_row_original% 65) s t c d
  · exact (source_vertex_row_original% 66) s t c d
  · exact (source_vertex_row_original% 67) s t c d
  · exact (source_vertex_row_original% 68) s t c d
  · exact (source_vertex_row_original% 69) s t c d
  · exact (source_vertex_row_original% 70) s t c d
  · exact (source_vertex_row_original% 71) s t c d
  · exact (source_vertex_row_original% 72) s t c d
  · exact (source_vertex_row_original% 73) s t c d
  · exact (source_vertex_row_original% 74) s t c d
  · exact (source_vertex_row_original% 75) s t c d
  · exact (source_vertex_row_original% 76) s t c d
  · exact (source_vertex_row_original% 77) s t c d
  · exact (source_vertex_row_original% 78) s t c d
  · exact (source_vertex_row_original% 79) s t c d
  · exact (source_vertex_row_original% 80) s t c d
  · exact (source_vertex_row_original% 81) s t c d
  · exact (source_vertex_row_original% 82) s t c d
  · exact (source_vertex_row_original% 83) s t c d
  · exact (source_vertex_row_original% 84) s t c d
  · exact (source_vertex_row_original% 85) s t c d
  · exact (source_vertex_row_original% 86) s t c d
  · exact (source_vertex_row_original% 87) s t c d
  · exact (source_vertex_row_original% 88) s t c d
  · exact (source_vertex_row_original% 89) s t c d
  · exact (source_vertex_row_original% 90) s t c d
  · exact (source_vertex_row_original% 91) s t c d
  · exact (source_vertex_row_original% 92) s t c d
  · exact (source_vertex_row_original% 93) s t c d
  · exact (source_vertex_row_original% 94) s t c d
  · exact (source_vertex_row_original% 95) s t c d
  · exact (source_vertex_row_original% 96) s t c d
end LowEnergy.ActualCandidateBra
