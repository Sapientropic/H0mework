import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraLeftGauge
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraLeftLorentz
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraLeftCoframe
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open ActualCandidateVertexEntries

theorem actual_entry_left (a : Fin 97) (B : Matrix Support Support ℂ) :
    tensor (entryMatrix a) B = left a B := by
  fin_cases a
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · simp [entryMatrix, vertexRow, tensor, left]
  · change tensor (fun i j => (source_vertex_row% 9) i.1 j.1 i.2 j.2) B = leftRow9 B
    exact actual_left9 B
  · change tensor (fun i j => (source_vertex_row% 10) i.1 j.1 i.2 j.2) B = leftRow10 B
    exact actual_left10 B
  · change tensor (fun i j => (source_vertex_row% 11) i.1 j.1 i.2 j.2) B = leftRow11 B
    exact actual_left11 B
  · change tensor (fun i j => (source_vertex_row% 12) i.1 j.1 i.2 j.2) B = leftRow12 B
    exact actual_left12 B
  · change tensor (fun i j => (source_vertex_row% 13) i.1 j.1 i.2 j.2) B = leftRow13 B
    exact actual_left13 B
  · change tensor (fun i j => (source_vertex_row% 14) i.1 j.1 i.2 j.2) B = leftRow14 B
    exact actual_left14 B
  · change tensor (fun i j => (source_vertex_row% 15) i.1 j.1 i.2 j.2) B = leftRow15 B
    exact actual_left15 B
  · change tensor (fun i j => (source_vertex_row% 16) i.1 j.1 i.2 j.2) B = leftRow16 B
    exact actual_left16 B
  · change tensor (fun i j => (source_vertex_row% 17) i.1 j.1 i.2 j.2) B = leftRow17 B
    exact actual_left17 B
  · change tensor (fun i j => (source_vertex_row% 18) i.1 j.1 i.2 j.2) B = leftRow18 B
    exact actual_left18 B
  · change tensor (fun i j => (source_vertex_row% 19) i.1 j.1 i.2 j.2) B = leftRow19 B
    exact actual_left19 B
  · change tensor (fun i j => (source_vertex_row% 20) i.1 j.1 i.2 j.2) B = leftRow20 B
    exact actual_left20 B
  · change tensor (fun i j => (source_vertex_row% 21) i.1 j.1 i.2 j.2) B = leftRow21 B
    exact actual_left21 B
  · change tensor (fun i j => (source_vertex_row% 22) i.1 j.1 i.2 j.2) B = leftRow22 B
    exact actual_left22 B
  · change tensor (fun i j => (source_vertex_row% 23) i.1 j.1 i.2 j.2) B = leftRow23 B
    exact actual_left23 B
  · change tensor (fun i j => (source_vertex_row% 24) i.1 j.1 i.2 j.2) B = leftRow24 B
    exact actual_left24 B
  · change tensor (fun i j => (source_vertex_row% 25) i.1 j.1 i.2 j.2) B = leftRow25 B
    exact actual_left25 B
  · change tensor (fun i j => (source_vertex_row% 26) i.1 j.1 i.2 j.2) B = leftRow26 B
    exact actual_left26 B
  · change tensor (fun i j => (source_vertex_row% 27) i.1 j.1 i.2 j.2) B = leftRow27 B
    exact actual_left27 B
  · change tensor (fun i j => (source_vertex_row% 28) i.1 j.1 i.2 j.2) B = leftRow28 B
    exact actual_left28 B
  · change tensor (fun i j => (source_vertex_row% 29) i.1 j.1 i.2 j.2) B = leftRow29 B
    exact actual_left29 B
  · change tensor (fun i j => (source_vertex_row% 30) i.1 j.1 i.2 j.2) B = leftRow30 B
    exact actual_left30 B
  · change tensor (fun i j => (source_vertex_row% 31) i.1 j.1 i.2 j.2) B = leftRow31 B
    exact actual_left31 B
  · change tensor (fun i j => (source_vertex_row% 32) i.1 j.1 i.2 j.2) B = leftRow32 B
    exact actual_left32 B
  · change tensor (fun i j => (source_vertex_row% 33) i.1 j.1 i.2 j.2) B = leftRow33 B
    exact actual_left33 B
  · change tensor (fun i j => (source_vertex_row% 34) i.1 j.1 i.2 j.2) B = leftRow34 B
    exact actual_left34 B
  · change tensor (fun i j => (source_vertex_row% 35) i.1 j.1 i.2 j.2) B = leftRow35 B
    exact actual_left35 B
  · change tensor (fun i j => (source_vertex_row% 36) i.1 j.1 i.2 j.2) B = leftRow36 B
    exact actual_left36 B
  · change tensor (fun i j => (source_vertex_row% 37) i.1 j.1 i.2 j.2) B = leftRow37 B
    exact actual_left37 B
  · change tensor (fun i j => (source_vertex_row% 38) i.1 j.1 i.2 j.2) B = leftRow38 B
    exact actual_left38 B
  · change tensor (fun i j => (source_vertex_row% 39) i.1 j.1 i.2 j.2) B = leftRow39 B
    exact actual_left39 B
  · change tensor (fun i j => (source_vertex_row% 40) i.1 j.1 i.2 j.2) B = leftRow40 B
    exact actual_left40 B
  · change tensor (fun i j => (source_vertex_row% 41) i.1 j.1 i.2 j.2) B = leftRow41 B
    exact actual_left41 B
  · change tensor (fun i j => (source_vertex_row% 42) i.1 j.1 i.2 j.2) B = leftRow42 B
    exact actual_left42 B
  · change tensor (fun i j => (source_vertex_row% 43) i.1 j.1 i.2 j.2) B = leftRow43 B
    exact actual_left43 B
  · change tensor (fun i j => (source_vertex_row% 44) i.1 j.1 i.2 j.2) B = leftRow44 B
    exact actual_left44 B
  · change tensor (fun i j => (source_vertex_row% 45) i.1 j.1 i.2 j.2) B = leftRow45 B
    exact actual_left45 B
  · change tensor (fun i j => (source_vertex_row% 46) i.1 j.1 i.2 j.2) B = leftRow46 B
    exact actual_left46 B
  · change tensor (fun i j => (source_vertex_row% 47) i.1 j.1 i.2 j.2) B = leftRow47 B
    exact actual_left47 B
  · change tensor (fun i j => (source_vertex_row% 48) i.1 j.1 i.2 j.2) B = leftRow48 B
    exact actual_left48 B
  · change tensor (fun i j => (source_vertex_row% 49) i.1 j.1 i.2 j.2) B = leftRow49 B
    exact actual_left49 B
  · change tensor (fun i j => (source_vertex_row% 50) i.1 j.1 i.2 j.2) B = leftRow50 B
    exact actual_left50 B
  · change tensor (fun i j => (source_vertex_row% 51) i.1 j.1 i.2 j.2) B = leftRow51 B
    exact actual_left51 B
  · change tensor (fun i j => (source_vertex_row% 52) i.1 j.1 i.2 j.2) B = leftRow52 B
    exact actual_left52 B
  · change tensor (fun i j => (source_vertex_row% 53) i.1 j.1 i.2 j.2) B = leftRow53 B
    exact actual_left53 B
  · change tensor (fun i j => (source_vertex_row% 54) i.1 j.1 i.2 j.2) B = leftRow54 B
    exact actual_left54 B
  · change tensor (fun i j => (source_vertex_row% 55) i.1 j.1 i.2 j.2) B = leftRow55 B
    exact actual_left55 B
  · change tensor (fun i j => (source_vertex_row% 56) i.1 j.1 i.2 j.2) B = leftRow56 B
    exact actual_left56 B
  · change tensor (fun i j => (source_vertex_row% 57) i.1 j.1 i.2 j.2) B = leftRow57 B
    exact actual_left57 B
  · change tensor (fun i j => (source_vertex_row% 58) i.1 j.1 i.2 j.2) B = leftRow58 B
    exact actual_left58 B
  · change tensor (fun i j => (source_vertex_row% 59) i.1 j.1 i.2 j.2) B = leftRow59 B
    exact actual_left59 B
  · change tensor (fun i j => (source_vertex_row% 60) i.1 j.1 i.2 j.2) B = leftRow60 B
    exact actual_left60 B
  · change tensor (fun i j => (source_vertex_row% 61) i.1 j.1 i.2 j.2) B = leftRow61 B
    exact actual_left61 B
  · change tensor (fun i j => (source_vertex_row% 62) i.1 j.1 i.2 j.2) B = leftRow62 B
    exact actual_left62 B
  · change tensor (fun i j => (source_vertex_row% 63) i.1 j.1 i.2 j.2) B = leftRow63 B
    exact actual_left63 B
  · change tensor (fun i j => (source_vertex_row% 64) i.1 j.1 i.2 j.2) B = leftRow64 B
    exact actual_left64 B
  · change tensor (fun i j => (source_vertex_row% 65) i.1 j.1 i.2 j.2) B = leftRow65 B
    exact actual_left65 B
  · change tensor (fun i j => (source_vertex_row% 66) i.1 j.1 i.2 j.2) B = leftRow66 B
    exact actual_left66 B
  · change tensor (fun i j => (source_vertex_row% 67) i.1 j.1 i.2 j.2) B = leftRow67 B
    exact actual_left67 B
  · change tensor (fun i j => (source_vertex_row% 68) i.1 j.1 i.2 j.2) B = leftRow68 B
    exact actual_left68 B
  · change tensor (fun i j => (source_vertex_row% 69) i.1 j.1 i.2 j.2) B = leftRow69 B
    exact actual_left69 B
  · change tensor (fun i j => (source_vertex_row% 70) i.1 j.1 i.2 j.2) B = leftRow70 B
    exact actual_left70 B
  · change tensor (fun i j => (source_vertex_row% 71) i.1 j.1 i.2 j.2) B = leftRow71 B
    exact actual_left71 B
  · change tensor (fun i j => (source_vertex_row% 72) i.1 j.1 i.2 j.2) B = leftRow72 B
    exact actual_left72 B
  · change tensor (fun i j => (source_vertex_row% 73) i.1 j.1 i.2 j.2) B = leftRow73 B
    exact actual_left73 B
  · change tensor (fun i j => (source_vertex_row% 74) i.1 j.1 i.2 j.2) B = leftRow74 B
    exact actual_left74 B
  · change tensor (fun i j => (source_vertex_row% 75) i.1 j.1 i.2 j.2) B = leftRow75 B
    exact actual_left75 B
  · change tensor (fun i j => (source_vertex_row% 76) i.1 j.1 i.2 j.2) B = leftRow76 B
    exact actual_left76 B
  · change tensor (fun i j => (source_vertex_row% 77) i.1 j.1 i.2 j.2) B = leftRow77 B
    exact actual_left77 B
  · change tensor (fun i j => (source_vertex_row% 78) i.1 j.1 i.2 j.2) B = leftRow78 B
    exact actual_left78 B
  · change tensor (fun i j => (source_vertex_row% 79) i.1 j.1 i.2 j.2) B = leftRow79 B
    exact actual_left79 B
  · change tensor (fun i j => (source_vertex_row% 80) i.1 j.1 i.2 j.2) B = leftRow80 B
    exact actual_left80 B
  · change tensor (fun i j => (source_vertex_row% 81) i.1 j.1 i.2 j.2) B = leftRow81 B
    exact actual_left81 B
  · change tensor (fun i j => (source_vertex_row% 82) i.1 j.1 i.2 j.2) B = leftRow82 B
    exact actual_left82 B
  · change tensor (fun i j => (source_vertex_row% 83) i.1 j.1 i.2 j.2) B = leftRow83 B
    exact actual_left83 B
  · change tensor (fun i j => (source_vertex_row% 84) i.1 j.1 i.2 j.2) B = leftRow84 B
    exact actual_left84 B
  · change tensor (fun i j => (source_vertex_row% 85) i.1 j.1 i.2 j.2) B = leftRow85 B
    exact actual_left85 B
  · change tensor (fun i j => (source_vertex_row% 86) i.1 j.1 i.2 j.2) B = leftRow86 B
    exact actual_left86 B
  · change tensor (fun i j => (source_vertex_row% 87) i.1 j.1 i.2 j.2) B = leftRow87 B
    exact actual_left87 B
  · change tensor (fun i j => (source_vertex_row% 88) i.1 j.1 i.2 j.2) B = leftRow88 B
    exact actual_left88 B
  · change tensor (fun i j => (source_vertex_row% 89) i.1 j.1 i.2 j.2) B = leftRow89 B
    exact actual_left89 B
  · change tensor (fun i j => (source_vertex_row% 90) i.1 j.1 i.2 j.2) B = leftRow90 B
    exact actual_left90 B
  · change tensor (fun i j => (source_vertex_row% 91) i.1 j.1 i.2 j.2) B = leftRow91 B
    exact actual_left91 B
  · change tensor (fun i j => (source_vertex_row% 92) i.1 j.1 i.2 j.2) B = leftRow92 B
    exact actual_left92 B
  · change tensor (fun i j => (source_vertex_row% 93) i.1 j.1 i.2 j.2) B = leftRow93 B
    exact actual_left93 B
  · change tensor (fun i j => (source_vertex_row% 94) i.1 j.1 i.2 j.2) B = leftRow94 B
    exact actual_left94 B
  · change tensor (fun i j => (source_vertex_row% 95) i.1 j.1 i.2 j.2) B = leftRow95 B
    exact actual_left95 B
  · change tensor (fun i j => (source_vertex_row% 96) i.1 j.1 i.2 j.2) B = leftRow96 B
    exact actual_left96 B
end LowEnergy.ActualCandidateBra
