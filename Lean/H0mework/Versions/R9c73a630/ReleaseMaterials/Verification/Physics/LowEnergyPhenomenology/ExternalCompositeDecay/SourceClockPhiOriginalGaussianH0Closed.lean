import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0FinalJoin
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0CoframeRecognition
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0Closed
open GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiOriginalGaussianH0FinalJoin
open SourceClockPhiOriginalGaussianH0NativeJoin SourceClockPhiMatchedDiffusionSource
open SourceClockPhiOriginalGaussianH0CoframeRecognition
open SourceCoframeCovariantAction SourceClockPhiCompleteHeatHamiltonianSource
open Filter
open scoped Topology
private theorem wholePairJet_of_coframe(f g:QuantumTest)
    (hco:deterministicPairJet f g+stochasticPairJet f g=
      sourcePair f ((completeCurrent covariantKinetic) g)):
    wholePairJet f g=sourcePair f ((completeCurrent GaussDiagonalHistory.diagonalAction) g):=by
  calc
    wholePairJet f g=
        (nativePairJet f g+localPairJet f g)+
          (deterministicPairJet f g+stochasticPairJet f g):=by unfold wholePairJet;ring
    _=sourcePair f (completeCurrent (nativeBase+localBase) g)+
        sourcePair f ((completeCurrent covariantKinetic) g):=by
          rw [native_local_jet_eq_completeCurrent,hco]
    _=sourcePair f (completeCurrent ((nativeBase+localBase)+covariantKinetic) g):=by
      rw [completeCurrent_add (nativeBase+localBase) covariantKinetic]
      simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
    _=sourcePair f ((completeCurrent GaussDiagonalHistory.diagonalAction) g):=by
      rw [original_H0_operator_split]
      have he:(nativeBase+localBase)+covariantKinetic=nativeBase+covariantKinetic+localBase:=by abel
      rw [he]
private theorem original_firstjet_of_coframe(f g:QuantumTest)
    (hco:deterministicPairJet f g+stochasticPairJet f g=
      sourcePair f ((completeCurrent covariantKinetic) g)):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (wholeGaussianHeatHamiltonianPair t ht f g-
        sourcePair f (GaussDiagonalHistory.diagonalAction g)) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 (sourcePair f ((completeCurrent GaussDiagonalHistory.diagonalAction) g))):=by
  rw [←wholePairJet_of_coframe f g hco]
  exact actual_original_whole_gaussian_first_jet_H0 f g

theorem actual_original_whole_pair_jet_Q_H0(f g:QuantumTest):
    wholePairJet f g=
      sourcePair f ((completeCurrent GaussDiagonalHistory.diagonalAction) g):=
  wholePairJet_of_coframe f g (actual_coframe_full36_first_jet_Q f g)

theorem actual_original_whole_gaussian_first_jet_Q_H0(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (wholeGaussianHeatHamiltonianPair t ht f g-
        sourcePair f (GaussDiagonalHistory.diagonalAction g)) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 (sourcePair f ((completeCurrent GaussDiagonalHistory.diagonalAction) g))):=
  original_firstjet_of_coframe f g (actual_coframe_full36_first_jet_Q f g)
end LowEnergy.SourceClockPhiOriginalGaussianH0Closed
