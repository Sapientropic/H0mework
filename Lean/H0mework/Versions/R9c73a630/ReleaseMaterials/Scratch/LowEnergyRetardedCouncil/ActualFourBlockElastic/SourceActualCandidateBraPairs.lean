import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraSourceLeft
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs0
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs1
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs2
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs3
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairs4
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexValues
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceCoframeSpinNormalOrder
open ActualCandidateVertexEntries ActualCandidateVertexValues ActualCandidateVertexLiterals
open scoped BigOperators InnerProductSpace

theorem actual_entry_pair (a b : Fin 97) :
    tensor (entryMatrix a) (entryMatrix b) = primalPairPoint a b := by
  rw [actual_entry_left]
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
  · change leftRow9 (entryMatrix b) = pairRow9 b
    exact actual_pair_row9 b
  · change leftRow10 (entryMatrix b) = pairRow10 b
    exact actual_pair_row10 b
  · change leftRow11 (entryMatrix b) = pairRow11 b
    exact actual_pair_row11 b
  · change leftRow12 (entryMatrix b) = pairRow12 b
    exact actual_pair_row12 b
  · change leftRow13 (entryMatrix b) = pairRow13 b
    exact actual_pair_row13 b
  · change leftRow14 (entryMatrix b) = pairRow14 b
    exact actual_pair_row14 b
  · change leftRow15 (entryMatrix b) = pairRow15 b
    exact actual_pair_row15 b
  · change leftRow16 (entryMatrix b) = pairRow16 b
    exact actual_pair_row16 b
  · rfl
  · rfl
  · change leftRow19 (entryMatrix b) = pairRow19 b
    exact actual_pair_row19 b
  · change leftRow20 (entryMatrix b) = pairRow20 b
    exact actual_pair_row20 b
  · change leftRow21 (entryMatrix b) = pairRow21 b
    exact actual_pair_row21 b
  · change leftRow22 (entryMatrix b) = pairRow22 b
    exact actual_pair_row22 b
  · rfl
  · rfl
  · change leftRow25 (entryMatrix b) = pairRow25 b
    exact actual_pair_row25 b
  · change leftRow26 (entryMatrix b) = pairRow26 b
    exact actual_pair_row26 b
  · change leftRow27 (entryMatrix b) = pairRow27 b
    exact actual_pair_row27 b
  · change leftRow28 (entryMatrix b) = pairRow28 b
    exact actual_pair_row28 b
  · rfl
  · rfl
  · change leftRow31 (entryMatrix b) = pairRow31 b
    exact actual_pair_row31 b
  · change leftRow32 (entryMatrix b) = pairRow32 b
    exact actual_pair_row32 b
  · change leftRow33 (entryMatrix b) = pairRow33 b
    exact actual_pair_row33 b
  · change leftRow34 (entryMatrix b) = pairRow34 b
    exact actual_pair_row34 b
  · rfl
  · rfl
  · change leftRow37 (entryMatrix b) = pairRow37 b
    exact actual_pair_row37 b
  · change leftRow38 (entryMatrix b) = pairRow38 b
    exact actual_pair_row38 b
  · change leftRow39 (entryMatrix b) = pairRow39 b
    exact actual_pair_row39 b
  · change leftRow40 (entryMatrix b) = pairRow40 b
    exact actual_pair_row40 b
  · rfl
  · rfl
  · change leftRow43 (entryMatrix b) = pairRow43 b
    exact actual_pair_row43 b
  · change leftRow44 (entryMatrix b) = pairRow44 b
    exact actual_pair_row44 b
  · change leftRow45 (entryMatrix b) = pairRow45 b
    exact actual_pair_row45 b
  · change leftRow46 (entryMatrix b) = pairRow46 b
    exact actual_pair_row46 b
  · change leftRow47 (entryMatrix b) = pairRow47 b
    exact actual_pair_row47 b
  · change leftRow48 (entryMatrix b) = pairRow48 b
    exact actual_pair_row48 b
  · change leftRow49 (entryMatrix b) = pairRow49 b
    exact actual_pair_row49 b
  · change leftRow50 (entryMatrix b) = pairRow50 b
    exact actual_pair_row50 b
  · change leftRow51 (entryMatrix b) = pairRow51 b
    exact actual_pair_row51 b
  · change leftRow52 (entryMatrix b) = pairRow52 b
    exact actual_pair_row52 b
  · rfl
  · rfl
  · change leftRow55 (entryMatrix b) = pairRow55 b
    exact actual_pair_row55 b
  · change leftRow56 (entryMatrix b) = pairRow56 b
    exact actual_pair_row56 b
  · change leftRow57 (entryMatrix b) = pairRow57 b
    exact actual_pair_row57 b
  · change leftRow58 (entryMatrix b) = pairRow58 b
    exact actual_pair_row58 b
  · change leftRow59 (entryMatrix b) = pairRow59 b
    exact actual_pair_row59 b
  · change leftRow60 (entryMatrix b) = pairRow60 b
    exact actual_pair_row60 b
  · change leftRow61 (entryMatrix b) = pairRow61 b
    exact actual_pair_row61 b
  · change leftRow62 (entryMatrix b) = pairRow62 b
    exact actual_pair_row62 b
  · change leftRow63 (entryMatrix b) = pairRow63 b
    exact actual_pair_row63 b
  · change leftRow64 (entryMatrix b) = pairRow64 b
    exact actual_pair_row64 b
  · change leftRow65 (entryMatrix b) = pairRow65 b
    exact actual_pair_row65 b
  · change leftRow66 (entryMatrix b) = pairRow66 b
    exact actual_pair_row66 b
  · change leftRow67 (entryMatrix b) = pairRow67 b
    exact actual_pair_row67 b
  · change leftRow68 (entryMatrix b) = pairRow68 b
    exact actual_pair_row68 b
  · change leftRow69 (entryMatrix b) = pairRow69 b
    exact actual_pair_row69 b
  · change leftRow70 (entryMatrix b) = pairRow70 b
    exact actual_pair_row70 b
  · change leftRow71 (entryMatrix b) = pairRow71 b
    exact actual_pair_row71 b
  · change leftRow72 (entryMatrix b) = pairRow72 b
    exact actual_pair_row72 b
  · change leftRow73 (entryMatrix b) = pairRow73 b
    exact actual_pair_row73 b
  · change leftRow74 (entryMatrix b) = pairRow74 b
    exact actual_pair_row74 b
  · change leftRow75 (entryMatrix b) = pairRow75 b
    exact actual_pair_row75 b
  · change leftRow76 (entryMatrix b) = pairRow76 b
    exact actual_pair_row76 b
  · change leftRow77 (entryMatrix b) = pairRow77 b
    exact actual_pair_row77 b
  · change leftRow78 (entryMatrix b) = pairRow78 b
    exact actual_pair_row78 b
  · change leftRow79 (entryMatrix b) = pairRow79 b
    exact actual_pair_row79 b
  · change leftRow80 (entryMatrix b) = pairRow80 b
    exact actual_pair_row80 b
  · change leftRow81 (entryMatrix b) = pairRow81 b
    exact actual_pair_row81 b
  · change leftRow82 (entryMatrix b) = pairRow82 b
    exact actual_pair_row82 b
  · change leftRow83 (entryMatrix b) = pairRow83 b
    exact actual_pair_row83 b
  · change leftRow84 (entryMatrix b) = pairRow84 b
    exact actual_pair_row84 b
  · change leftRow85 (entryMatrix b) = pairRow85 b
    exact actual_pair_row85 b
  · change leftRow86 (entryMatrix b) = pairRow86 b
    exact actual_pair_row86 b
  · change leftRow87 (entryMatrix b) = pairRow87 b
    exact actual_pair_row87 b
  · change leftRow88 (entryMatrix b) = pairRow88 b
    exact actual_pair_row88 b
  · change leftRow89 (entryMatrix b) = pairRow89 b
    exact actual_pair_row89 b
  · change leftRow90 (entryMatrix b) = pairRow90 b
    exact actual_pair_row90 b
  · change leftRow91 (entryMatrix b) = pairRow91 b
    exact actual_pair_row91 b
  · change leftRow92 (entryMatrix b) = pairRow92 b
    exact actual_pair_row92 b
  · change leftRow93 (entryMatrix b) = pairRow93 b
    exact actual_pair_row93 b
  · change leftRow94 (entryMatrix b) = pairRow94 b
    exact actual_pair_row94 b
  · change leftRow95 (entryMatrix b) = pairRow95 b
    exact actual_pair_row95 b
  · change leftRow96 (entryMatrix b) = pairRow96 b
    exact actual_pair_row96 b

theorem actual_source_entry_matrix (dual : Bool) (a : Fin 97) (i j : Support) :
    MixedSpectatorContactVertices.sourceVertex (0 : Fin 4 → ℂ) a
        (supportMode dual i) (supportMode dual j) =
      if dual then -star (entryMatrix a i j) else entryMatrix a i j := by
  rcases i with ⟨s,c⟩
  rcases j with ⟨t,d⟩
  rw [actual_source_literals]
  simp only [literalVertex, actual_primal_row, entryMatrix]

/-- The actual97 source matrices on the actual mixed candidate produce their
own fixed-bra CAR contraction. Both independent source branches are retained. -/
theorem actual_source_pair (dual : Bool) (a b : Fin 97) :
    inner ℂ (bra dual)
      (normalFiber (MixedSpectatorContactVertices.sourceVertex (0 : Fin 4 → ℂ) a)
        (MixedSpectatorContactVertices.sourceVertex (0 : Fin 4 → ℂ) b)
        (MixedSpectatorCandidate.candidate dual)) = pairPoint dual a b := by
  rw [actual_bra_normal]
  erw [actual_bra_tensor]
  simp_rw [actual_source_entry_matrix]
  cases dual
  · change tensor (entryMatrix a) (entryMatrix b) = primalPairPoint a b
    exact actual_entry_pair a b
  · change tensor (fun i j => -star (entryMatrix a i j))
        (fun i j => -star (entryMatrix b i j)) = star (primalPairPoint a b)
    rw [actual_tensor_neg_star, actual_entry_pair]

theorem actual_scalar_source_pair_zero (dual : Bool) (a b : Fin 70) :
    inner ℂ (bra dual)
      (normalFiber (MixedSpectatorScalar61Exchange.sourceVertex a)
        (MixedSpectatorScalar61Exchange.sourceVertex b)
        (MixedSpectatorCandidate.candidate dual)) = 0 := by
  rw [actual_bra_normal]
  erw [actual_bra_tensor]
  have ha : (fun i j => MixedSpectatorScalar61Exchange.sourceVertex a
      (supportMode dual i) (supportMode dual j)) = (0 : Matrix Support Support ℂ) := by
    ext i j
    exact actual_scalar_entry_zero dual a i j
  have hb : (fun i j => MixedSpectatorScalar61Exchange.sourceVertex b
      (supportMode dual i) (supportMode dual j)) = (0 : Matrix Support Support ℂ) := by
    ext i j
    exact actual_scalar_entry_zero dual b i j
  rw [ha,hb]
  simp [tensor]

end LowEnergy.ActualCandidateBra
