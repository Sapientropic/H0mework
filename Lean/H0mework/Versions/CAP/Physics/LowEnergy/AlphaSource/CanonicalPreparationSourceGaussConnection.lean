import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGaussColorTorque
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore


def sourceColorChargeFiber : FockFiber→L[ℂ] FockFiber := quantizer (chargeMatrix (colorGenerator 2))

def sourceColorConnectionFiber (v : Ambient) (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber :=
  nativeFock (inverseL z v).1*sourceColorChargeFiber-sourceColorChargeFiber*nativeFock (inverseL z v).1

private theorem directional_constant (v : Ambient) (T : FockFiber→L[ℂ] FockFiber) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    fderiv ℝ (fun w : SourceCoordinateSlice=>T (f w)) z (direction v z)=
      T (fderiv ℝ f z (direction v z)) := by
  have h:=(T.restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change (fderiv ℝ ((T.restrictScalars ℝ) ∘ f) z) (direction v z)=_
  rw [h.fderiv]
  rfl

theorem sourceColor_directional (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (chargeAction (colorGenerator 2) f) z=
      sourceColorChargeFiber (directional v f z) := by
  change fderiv ℝ (fun w : SourceCoordinateSlice=>sourceColorChargeFiber (f w)) z (direction v z)=_
  exact directional_constant v sourceColorChargeFiber f z

theorem sourceColor_covariant_connection (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    covariantMomentum v (chargeAction (colorGenerator 2) f) z-
      chargeAction (colorGenerator 2) (covariantMomentum v f) z=
        (-Complex.I) • sourceColorConnectionFiber v z (f z) := by
  change (-Complex.I) • (directional v (chargeAction (colorGenerator 2) f) z+
    connection v z (sourceColorChargeFiber (f z)))-
      sourceColorChargeFiber ((-Complex.I) • (directional v f z+connection v z (f z)))=_
  rw [sourceColor_directional,map_smul,map_add]
  simp only [smul_add]
  change (-Complex.I) • sourceColorChargeFiber (directional v f z)+
      (-Complex.I) • (nativeFock (inverseL z v).1 (sourceColorChargeFiber (f z)))-
      ((-Complex.I) • sourceColorChargeFiber (directional v f z)+
        (-Complex.I) • sourceColorChargeFiber (nativeFock (inverseL z v).1 (f z)))=_
  simp only [sourceColorConnectionFiber,sub_apply,mul_apply_eq_comp,smul_sub]
  abel

theorem sourceColorCharge_hermitian : (chargeMatrix (colorGenerator 2)).conjTranspose=chargeMatrix (colorGenerator 2) := by
  simp only [chargeMatrix,Matrix.conjTranspose_smul,nativeFull_skew,Complex.star_def,Complex.conj_I,
    smul_neg,neg_smul,neg_neg]

theorem sourceColorCharge_pair (f g : QuantumTest) :
    sourcePair f (chargeAction (colorGenerator 2) g)=sourcePair (chargeAction (colorGenerator 2) f) g :=
  GaussQuantumMultiplier.action_pair _ _ (fun _=>sourceColorCharge_hermitian) f g

end LowEnergy.PreparationVacuumPhysicalGaussColorTorque
