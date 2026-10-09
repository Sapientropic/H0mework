import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0NativeJoin
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0LocalSpinNumber
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0FinalJoin
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceClockPhiOriginalGaussianH0Recognition SourceClockPhiOriginalGaussianH0FirstJet
open SourceClockPhiOriginalGaussianH0RealPrimitives SourceClockPhiOriginalGaussianH0KineticPrimitives
open SourceClockPhiOriginalGaussianH0NativeJoin SourceClockPhiOriginalGaussianH0LocalSpinNumber
open SourceScalarVirialBulk SourceScalarDoubleCurrent SourceCoframeCovariantSquare
open GaussNativePotential SourceCoframeVolume SourceCoframeVolumeCurrent
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth

def localBase:End:=spinRemainder+GaussCoframeForm.numberShift+V

theorem local_three_jet_eq_completeCurrent(f g:QuantumTest):
    localPairJet f g=sourcePair f (completeCurrent localBase g):=by
  have hq:completeCurrent localBase=(-12:ℂ) • (U*spinRemainder)+
      (-12:ℂ) • (U*GaussCoframeForm.numberShift)+(24:ℂ) • (U*V):=by
    unfold localBase
    rw [completeCurrent_add,completeCurrent_add,spin_remainder_complete_current,
      number_shift_complete_current,coframe_volume_complete_current]
  change (-12:ℂ)*sourcePair f (U (spinRemainder g))+
      (-12:ℂ)*sourcePair f (U (GaussCoframeForm.numberShift g))+
      (24:ℂ)*sourcePair f (U (V g))=sourcePair f (completeCurrent localBase g)
  rw [hq]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
theorem native_local_jet_eq_completeCurrent(f g:QuantumTest):
    nativePairJet f g+localPairJet f g=
      sourcePair f (completeCurrent (nativeBase+localBase) g):=by
  rw [native_eight_jet_eq_completeCurrent,local_three_jet_eq_completeCurrent,
    completeCurrent_add]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]

private abbrev centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*‖scalarField z‖^2
private abbrev vacLinValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*inner ℝ vacuum (scalarField z)
private abbrev vacConstValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*‖vacuum‖^2
private abbrev spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*volume z/2*∑i:Fin 3,∑j:Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem potential_decompose(z:SourceCoordinateSlice):
    potential z=centerValue z-2*vacLinValue z+vacConstValue z+spatialValue z+magneticPotential z:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hn:=norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centerValue vacLinValue vacConstValue spatialValue
  rw [real_inner_self_eq_norm_sq,hn]
  ring
private theorem potential_action_decompose:
    multiply potential potential_smooth=centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (potential z:ℂ) • f z=(centerValue z:ℂ) • f z-
    (2:ℂ) • ((vacLinValue z:ℂ) • f z)+(vacConstValue z:ℂ) • f z+
    (spatialValue z:ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]

theorem original_H0_operator_split:
    GaussDiagonalHistory.diagonalAction=nativeBase+
      SourceCoframeCovariantAction.covariantKinetic+localBase:=by
  unfold GaussDiagonalHistory.diagonalAction GaussNativeForm.nativeAction
  rw [potential_action_decompose,SourceCoframeCovariantSquare.original_coframe_covariant]
  unfold nativeBase localBase V
  abel

end LowEnergy.SourceClockPhiOriginalGaussianH0FinalJoin
