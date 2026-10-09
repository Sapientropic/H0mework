import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeComplementJointSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NativePointReturn
open GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussDiagonalHistory
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiOriginalGaussianH0NativeJoin
open SourceClockPhiOriginalGaussianH0FinalJoin SourceClockPhiMatchedDiffusionSource
open SourceCoframeCovariantAction PositiveClockGenerator ClockPhiHeatCorrectedCovarianceSource
open MeasureTheory
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1

theorem actual_native_complement_operator:
    nativeComplement=nativeBase+localBase:=by
  unfold nativeComplement
  rw [original_H0_operator_split]
  abel

theorem actual_native_complement_Q_jet(f g:QuantumTest):
    sourcePair f (completeCurrent nativeComplement g)=nativePairJet f g+localPairJet f g:=by
  rw [actual_native_complement_operator]
  exact (native_local_jet_eq_completeCurrent f g).symm

/-- The joint native/local price consumes the original complete two-noise source directly. -/
theorem actual_corrected_native_joint_gaussian(s:ℝ)(hs:0<s)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore s hs x.1 x.2 f)
      (completeCurrent nativeComplement (correctedCompleteCore s hs x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore s hs x.1 x.2 f)
      (completeCurrent nativeComplement (correctedCompleteCore s hs x.1 x.2 g)) ∂γ.prod γ)=
      nativePositiveMean s hs f g+localPositiveMean s hs f g:=by
  have hN:=actual_corrected_native_jet_gaussian s hs f g
  have hL:=actual_corrected_local_jet_gaussian s hs f g
  simp_rw [actual_native_complement_Q_jet]
  refine ⟨hN.1.add hL.1,?_⟩
  rw [integral_add hN.1 hL.1,hN.2,hL.2]

end LowEnergy.NativePointReturn
