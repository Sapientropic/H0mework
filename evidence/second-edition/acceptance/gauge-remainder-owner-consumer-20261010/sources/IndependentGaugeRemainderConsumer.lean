import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstFullGaugeRemainder
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance IndependentGaugeRemainderInstance1 : DecidableEq Quantum.Index:=Classical.decEq _
local instance IndependentGaugeRemainderInstance2 : DecidableEq Mode:=Classical.decEq _
local instance IndependentGaugeRemainderInstance3 : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance IndependentGaugeRemainderInstance4 : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance IndependentGaugeRemainderInstance5 : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance IndependentGaugeRemainderInstance6 : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance IndependentGaugeRemainderInstance7 : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance IndependentGaugeRemainderInstance8 : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance IndependentGaugeRemainderInstance9 : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationVacuumPhysicalChargedFieldFactor
open SourcePropagationNativeActionHessian StageNineLorentzConnectionVariation
open StageNineP286BracketCalculus StageNineP286InfinitesimalGaugeTransformation
open SU7MotherGaugeTheory StageNineP286GaugeConnectionVariation
local instance IndependentGaugeRemainderInstance10 : Fintype P286CoordinateIndex:=StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype


example (v : Fin 4→ℂ) (row : Fin 289) :
    sourceChargedNativeFrameJet v row 1=
      ∑mu : Fin 4,v mu*(sourceEnergyAxisField 1 mu row:ℂ) := sourceFirstLiteralField_generated v row

example (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) :
    configurationRay (sourceFirstModeGauge imaginary omega k c)
      (sourceFirstModeRemainder imaginary omega k c) 1=sourceFirstModeTangent imaginary omega k := sourceFirstModeRemainder_original imaginary omega k c

example (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv ((sourceFirstModeRemainder imaginary omega k c).gaugeConnection x mu)=
      (∑a : Fin 4,(-sourceFirstGaugeQuadratureDerivative imaginary omega k x a) • sourceFirstGaugeRemainderConnection a mu)-
      sourceFirstGaugeQuadrature imaginary omega k x • lie sourceFirstTemporalLie (actualConnection c x mu) := sourceFirstModeRemainder_connection imaginary omega k c x mu

end LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
#print axioms LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder.sourceFirstLiteralField_generated
#print axioms LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder.sourceFirstModeRemainder_original
#print axioms LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder.sourceFirstModeRemainder_connection
