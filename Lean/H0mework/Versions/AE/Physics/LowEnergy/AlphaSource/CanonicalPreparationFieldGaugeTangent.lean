import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceTotalFormJets

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldConstraintResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeVariation
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

open GaussNativePotential GaussNativeMatter
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift

open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumNonlinearFieldCurve
open SU7ExteriorBreakingYukawa GaussNativeEnergy StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity

open SourceQuantumScalarChart
open GaussLiveMomentum GaussDensityCore GaussFockPair GaussMomentumAdjoint
open MeasureTheory
open scoped Distributions InnerProductSpace

open PreparationVacuumSourceActionJets StageNineCoframeGravityGaugeRegularity

-- All twelve native gauge directions come from the original field slots.
def fieldAmbient (f : Field289) : Ambient :=
  (fieldScalar f,WithLp.toLp 2 (fun i : Fin 3=>fieldGauge f i.succ))

def gaugeParameters (f : Field289) (z : SourceCoordinateSlice) : Split := inverseL z (fieldAmbient f)
def gaugeOrbitParameter (f : Field289) (z : SourceCoordinateSlice) : NativeLie := (gaugeParameters f z).1
def gaugeSliceDirection (f : Field289) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (0,(gaugeParameters f z).2)

theorem gauge_tangent_reconstruction (f : Field289) (z : physicalChart) :
    orbitMap z.val (gaugeOrbitParameter f z.val)+sliceMap (gaugeParameters f z.val).2=fieldAmbient f :=
  inverse_right z (fieldAmbient f)

theorem scalar_tangent_reconstruction (f : Field289) (z : physicalChart) :
    scalarP286ActionBilinear (gaugeOrbitParameter f z.val) (scalarField z.val)+
      ((gaugeParameters f z.val).2.1:Scalar)=fieldScalar f :=
  congrArg Prod.fst (gauge_tangent_reconstruction f z)

theorem spatial_gauge_tangent_reconstruction (f : Field289) (z : physicalChart) (i : Fin 3) :
    SourceCartanCubic.gaugeCoordinate i (nativeGauge (gaugeOrbitParameter f z.val) (z.val.2.2:Gauge))+
      SourceCartanCubic.gaugeCoordinate i ((gaugeParameters f z.val).2.2:Gauge)=fieldGauge f i.succ := by
  have h:=congrArg Prod.snd (gauge_tangent_reconstruction f z)
  change nativeGauge (gaugeOrbitParameter f z.val) (z.val.2.2:Gauge)+
    ((gaugeParameters f z.val).2.2:Gauge)=(fieldAmbient f).2 at h
  have read:=congrArg (fun A : Gauge=>SourceCartanCubic.gaugeCoordinate i A) h
  rw [map_add] at read
  exact read

theorem gauge_tangent_unique (f : Field289) (z : physicalChart) (a : NativeLie) (h : Slice)
    (same : orbitMap z.val a+sliceMap h=fieldAmbient f) :
    (a,h)=gaugeParameters f z.val := by
  apply (splitMap_injective z)
  exact same.trans (inverse_right z (fieldAmbient f)).symm

theorem gaugeParameters_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (gaugeParameters f) z.val := (inverse_smooth z).clm_apply contDiffAt_const

theorem gaugeSlice_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (gaugeSliceDirection f) z.val :=
  contDiffAt_const.prodMk (gaugeParameters_smooth f z).snd

theorem gaugeOrbit_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (gaugeOrbitParameter f) z.val := (gaugeParameters_smooth f z).fst

theorem gaugeParameters_first (f : Field289) (h : SourceCoordinateSlice) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>gaugeParameters f (z.val+r • h))
      (inverseFirst h z.val (fieldAmbient f)) 0 := by
  have generated:=(inverse_curve_first h z).clm_apply (hasDerivAt_const (0:ℝ) (fieldAmbient f))
  simp only [zero_smul,add_zero,map_zero] at generated
  convert! generated using 1

theorem gaugeParameters_second (f : Field289) (h : SourceCoordinateSlice) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>inverseFirst h (z.val+r • h) (fieldAmbient f))
      (inverseSecond h h z.val (fieldAmbient f)) 0 := by
  have generated:=(inverse_curve_second h z).clm_apply (hasDerivAt_const (0:ℝ) (fieldAmbient f))
  simpa only [zero_smul,add_zero,map_zero] using generated

-- The vertical part acts on the original CAR fiber; it is not discarded as a zero Ward direction.
theorem original_covariant_field_core (f : Field289) (test : QuantumTest) (z : SourceCoordinateSlice) :
    covariantMomentum (fieldAmbient f) test z=(-Complex.I) •
      (fderiv ℝ test z (gaugeSliceDirection f z)+nativeFock (gaugeOrbitParameter f z) (test z)) := rfl

theorem original_covariant_field_pair (f : Field289) (left right : QuantumTest) :
    sourcePair left (covariantMomentum (fieldAmbient f) right)=
      sourcePair (GaussMomentumAdjoint.adjoint (fieldAmbient f) left) right :=
  GaussMomentumAdjoint.momentum_pair (fieldAmbient f) left right

theorem fieldAmbient_add (f g : Field289) : fieldAmbient (f+g)=fieldAmbient f+fieldAmbient g := by
  apply Prod.ext
  · exact fieldScalar_add f g
  · apply PiLp.ext
    intro i
    exact fieldGauge_add f g i.succ

theorem fieldAmbient_smul (r : ℝ) (f : Field289) : fieldAmbient (r • f)=r • fieldAmbient f := by
  apply Prod.ext
  · exact fieldScalar_smul r f
  · apply PiLp.ext
    intro i
    exact fieldGauge_smul r f i.succ

theorem gaugeParameters_add (f g : Field289) (z : SourceCoordinateSlice) :
    gaugeParameters (f+g) z=gaugeParameters f z+gaugeParameters g z := by
  rw [gaugeParameters,fieldAmbient_add,map_add]
  rfl

theorem gaugeParameters_smul (r : ℝ) (f : Field289) (z : SourceCoordinateSlice) :
    gaugeParameters (r • f) z=r • gaugeParameters f z := by
  rw [gaugeParameters,fieldAmbient_smul,map_smul]
  rfl

end LowEnergy.PreparationVacuumFieldConstraintResponse
