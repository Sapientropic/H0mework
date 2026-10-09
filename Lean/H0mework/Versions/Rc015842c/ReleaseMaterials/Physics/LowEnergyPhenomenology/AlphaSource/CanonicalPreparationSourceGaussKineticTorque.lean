import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussConnection

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




open scoped ContDiff

abbrev QuantumEnd := QuantumTest→ₗ[ℂ] QuantumTest

def sourceColorCovariantTorque (v : Ambient) : QuantumEnd :=
  (covariantMomentum v).comp (chargeAction (colorGenerator 2))-
    (chargeAction (colorGenerator 2)).comp (covariantMomentum v)

theorem sourceColorCovariantTorque_generated (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceColorCovariantTorque v f z=(-Complex.I) • sourceColorConnectionFiber v z (f z) :=
  sourceColor_covariant_connection v f z

private theorem pair_sub_right (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_add_right (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_add_left (f g h : QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]

private theorem covariant_decomposition (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (chargeAction (colorGenerator 2) f)=
      chargeAction (colorGenerator 2) (covariantMomentum v f)+sourceColorCovariantTorque v f := by
  change _=chargeAction (colorGenerator 2) (covariantMomentum v f)+
    (covariantMomentum v (chargeAction (colorGenerator 2) f)-chargeAction (colorGenerator 2) (covariantMomentum v f))
  abel

private theorem scalar_charge (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
    GaussNativeForm.multiply c smooth (chargeAction (colorGenerator 2) f)=
      chargeAction (colorGenerator 2) (GaussNativeForm.multiply c smooth f) := by
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • sourceColorChargeFiber (f z)=sourceColorChargeFiber ((c z : ℂ) • f z)
  exact (map_smul sourceColorChargeFiber (c z : ℂ) (f z)).symm

/-- Both covariant legs retain the original inverseL connection torque. -/
def sourceNativeSandwichTorque (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) : ℂ :=
  sourcePair (covariantMomentum v f) (GaussNativeForm.multiply c smooth (sourceColorCovariantTorque w g))-
    sourcePair (sourceColorCovariantTorque v f) (GaussNativeForm.multiply c smooth (covariantMomentum w g))

theorem sourceNativeSandwichWard (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.sandwich v w c smooth (chargeAction (colorGenerator 2) g)-
      chargeAction (colorGenerator 2) (GaussNativeForm.sandwich v w c smooth g))=
      sourceNativeSandwichTorque v w c smooth f g := by
  rw [pair_sub_right,sourceColorCharge_pair]
  change sourcePair f (GaussMomentumAdjoint.adjoint v (GaussNativeForm.multiply c smooth (covariantMomentum w (chargeAction (colorGenerator 2) g))))-
    sourcePair (chargeAction (colorGenerator 2) f) (GaussMomentumAdjoint.adjoint v (GaussNativeForm.multiply c smooth (covariantMomentum w g)))=_
  rw [GaussNativeForm.adjoint_pair,GaussNativeForm.adjoint_pair,covariant_decomposition w g,covariant_decomposition v f,
    map_add,pair_add_right,pair_add_left,scalar_charge,sourceColorCharge_pair]
  unfold sourceNativeSandwichTorque
  abel


def sourceColorWardOperator (A : QuantumEnd) : QuantumEnd :=
  A.comp (chargeAction (colorGenerator 2))-(chargeAction (colorGenerator 2)).comp A

private def sourceColorWardLinear : QuantumEnd→ₗ[ℂ] QuantumEnd where
  toFun:=sourceColorWardOperator
  map_add' A B:=by
    apply LinearMap.ext
    intro f
    simp only [sourceColorWardOperator,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.add_apply,map_add]
    abel
  map_smul' c A:=by
    apply LinearMap.ext
    intro f
    simp only [sourceColorWardOperator,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,map_smul,smul_sub,RingHom.id_apply]

private theorem sourceColorWard_multiply (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    sourceColorWardOperator (GaussNativeForm.multiply c smooth)=0 := by
  apply LinearMap.ext
  intro f
  exact sub_eq_zero.mpr (scalar_charge c smooth f)

theorem sourceNativeOperator_generated :
    sourceColorWardOperator GaussNativeForm.nativeAction=
      (1/2 : ℂ) • (∑ a : GaussNativeForm.ScalarIndex,
        sourceColorWardOperator (GaussNativeForm.sandwich (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
          GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth))+
      (1/2 : ℂ) • (∑ a : GaussNativeForm.LieIndex,∑ i : Fin 3,∑ j : Fin 3,
        sourceColorWardOperator (GaussNativeForm.sandwich (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
          (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j))) := by
  change sourceColorWardLinear GaussNativeForm.nativeAction=_
  rw [GaussNativeForm.nativeAction,map_add,map_add]
  change sourceColorWardLinear GaussNativeForm.scalarKinetic+sourceColorWardLinear GaussNativeForm.gaugeKinetic+
    sourceColorWardOperator (GaussNativeForm.multiply potential potential_smooth)=_
  rw [sourceColorWard_multiply,add_zero]
  unfold GaussNativeForm.scalarKinetic GaussNativeForm.gaugeKinetic
  simp only [map_smul,map_sum]
  rfl

def sourceNativeTorque (f g : QuantumTest) : ℂ :=
  (1/2 : ℂ) * (∑ a : GaussNativeForm.ScalarIndex,
    sourceNativeSandwichTorque (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
      GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth f g)+
  (1/2 : ℂ) * (∑ a : GaussNativeForm.LieIndex,∑ i : Fin 3,∑ j : Fin 3,
    sourceNativeSandwichTorque (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
      (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j) f g)

private theorem pair_sum_right {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι→QuantumTest) :
    sourcePair f (∑ i,g i)=∑ i,sourcePair f (g i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_smul_right (f g : QuantumTest) (c : ℂ) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

theorem sourceNativeActionWard (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.nativeAction (chargeAction (colorGenerator 2) g)-
      chargeAction (colorGenerator 2) (GaussNativeForm.nativeAction g))=sourceNativeTorque f g := by
  change sourcePair f (sourceColorWardOperator GaussNativeForm.nativeAction g)=_
  rw [sourceNativeOperator_generated]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,pair_add_right,pair_smul_right,pair_sum_right]
  unfold sourceNativeTorque
  apply congrArg₂ (fun x y : ℂ=>x+y)
  · apply congrArg ((1/2 : ℂ)*·)
    apply Finset.sum_congr rfl
    intro a _
    exact sourceNativeSandwichWard (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
      GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth f g
  · apply congrArg ((1/2 : ℂ)*·)
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact sourceNativeSandwichWard (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
      (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j) f g

end LowEnergy.PreparationVacuumPhysicalGaussColorTorque
