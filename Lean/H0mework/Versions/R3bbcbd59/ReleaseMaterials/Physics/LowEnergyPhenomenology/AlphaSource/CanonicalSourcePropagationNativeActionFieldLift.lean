import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalSourceColumns
import H0mework.Physics.DualVariation.MotherAction
import H0mework.Versions.AB.Physics.LowEnergyActiveGauge.Phase
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineLorentzConnectionVariation
open DiracExteriorMatterAction Stage9C.Material.SpinPair SourceQuantumScalarChart
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction PreparationVacuumLowerClassical
open StageNineDiracDualFormNativePointwiseActionJetCarrier StageNineDiracDualFormNativeJointResidualCarrier
open scoped BigOperators

def primalInsertion (f : Field289) : DiracExteriorMatterCarrier :=
  ∑ spin : Fin 4, ∑ color : Fin 3, fieldPrimalComplex f spin color • sourceTripletLeg spin color

/-- The independent dual uses the original exterior basis coefficients, with no conjugation. -/
def dualInsertion (f : Field289) : Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun v := ∑ spin : Fin 4, ∑ color : Fin 3,
    fieldDualComplex f spin color * sourceTripletRead (v spin) color
  map_add' := by
    intro v w
    change (∑ spin : Fin 4, ∑ color : Fin 3, fieldDualComplex f spin color *
      (SU7ExteriorMatterRestriction.su7ExteriorBasis 2).repr
        ((v spin).2.1 + (w spin).2.1) (sourceTripletIndex color)) = _
    simp only [map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib, sourceTripletRead]
  map_smul' := by
    intro c v
    change (∑ spin : Fin 4, ∑ color : Fin 3, fieldDualComplex f spin color *
      (SU7ExteriorMatterRestriction.su7ExteriorBasis 2).repr
        (c • (v spin).2.1) (sourceTripletIndex color)) = _
    simp only [sourceTripletRead, map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro color _
    ring

def gaugeBInsertion (f : Field289) (pair : Fin 6) : SU7MotherLieAlgebra.P286LieBlockData :=
  p286CoordinateEquiv.symm (∑ a : Fin 12, fieldGaugeB f pair a • originalUnit a)

/-- All nine original field groups vary in the same actual holonomic configuration. -/
def nativeConfiguration (signal : BasePoint → Field289) : StageNineHolonomicConfiguration where
  coframe point := actual.coframe point + fieldCoframe (signal point)
  gravityConnection point := actual.gravityConnection point +
    lorentzSkewConnectionOfBivectorOneForm (fieldLorentz (signal point))
  gravityAuxiliary point := actual.gravityAuxiliary point + fieldGravityB (signal point)
  gravitySimplicityMultiplier point := actual.gravitySimplicityMultiplier point + fieldMultiplier (signal point)
  gaugeConnection point mu := actual.gaugeConnection point mu +
    p286CoordinateEquiv.symm (fieldGauge (signal point) mu)
  gaugeAuxiliary point pair := actual.gaugeAuxiliary point pair + gaugeBInsertion (signal point) pair
  scalar point := actual.scalar point + fieldScalar (signal point)
  matter point := actual.matter point + diracMatrixMatterAction
    (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point) (primalInsertion (signal point))
  conjugateMatter point := actual.conjugateMatter point + (dualInsertion (signal point)).comp
    (diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point))

theorem primalInsertion_zero : primalInsertion 0 = 0 := by
  simp [primalInsertion, fieldPrimalComplex, fieldPrimal]

theorem dualInsertion_zero : dualInsertion 0 = 0 := by
  apply LinearMap.ext
  intro v
  simp [dualInsertion, fieldDualComplex, fieldDual]

theorem gaugeBInsertion_zero (pair : Fin 6) : gaugeBInsertion 0 pair = 0 := by
  simp [gaugeBInsertion, fieldGaugeB]

theorem nativeConfiguration_zero : nativeConfiguration (fun _ => 0) = actual := by
  ext point
  all_goals simp [nativeConfiguration, fieldCoframe, fieldLorentz, fieldGravityB,
    fieldMultiplier, fieldGauge, fieldScalar, primalInsertion_zero, dualInsertion_zero,
    gaugeBInsertion_zero, lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix]

abbrev NativeFirstJet := Field289 × (Fin 4 → Field289)

def affineSignal (jet : NativeFirstJet) (point : BasePoint) : Field289 :=
  jet.1 + ∑ mu : Fin 4, point mu • jet.2 mu

theorem affineSignal_zero (jet : NativeFirstJet) : affineSignal jet 0 = jet.1 := by
  simp [affineSignal]

def jetDerivative (gradient : Fin 4 → Field289) : BasePoint →L[ℝ] Field289 :=
  ∑ mu : Fin 4, (EuclideanSpace.proj mu : BasePoint →L[ℝ] ℝ).smulRight (gradient mu)

theorem affineSignal_hasFDerivAt (jet : NativeFirstJet) (point : BasePoint) :
    HasFDerivAt (affineSignal jet) (jetDerivative jet.2) point := by
  have derivative := ((jetDerivative jet.2).hasFDerivAt (x := point)).const_add jet.1
  convert! derivative using 1

theorem affineSignal_directionalDerivative (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (affineSignal jet) 0 mu = jet.2 mu := by
  rw [fieldDirectionalDerivative, (affineSignal_hasFDerivAt jet 0).fderiv]
  simp [jetDerivative, coordinateDirection]

def nativePoint (signal : BasePoint → Field289) (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField (nativeConfiguration signal) point

def nativeDensity (signal : BasePoint → Field289) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource
    0 point (nativePoint signal point)

theorem nativePoint_zero (point : BasePoint) :
    nativePoint (fun _ => 0) point = toContinuumPointField actual point := by
  rw [nativePoint, nativeConfiguration_zero]

theorem nativeDensity_original (signal : BasePoint → Field289) (point : BasePoint) :
    nativeDensity signal point = generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      positiveSmoothUnifiedSource (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      0 point
      (toContinuumPointField (nativeConfiguration signal) point) := rfl

def nativeJetDensity (jet : NativeFirstJet) : ℝ := nativeDensity (affineSignal jet) 0

theorem nativeJetDensity_original (jet : NativeFirstJet) :
    nativeJetDensity jet = generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      positiveSmoothUnifiedSource (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      0 0 (toContinuumPointField (nativeConfiguration (affineSignal jet)) 0) := rfl

def nativeActionJet (signal : BasePoint → Field289) (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet positiveSmoothUnifiedSource
    (nativeConfiguration signal) point

def nativeEuler (signal : BasePoint → Field289) (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet positiveSmoothUnifiedSource point
    (nativeActionJet signal point)

theorem nativeEuler_original (signal : BasePoint → Field289) (point : BasePoint) :
    nativeEuler signal point = diracDualFormNativePointwiseJointResidual
      positiveSmoothUnifiedSource (nativeConfiguration signal) point := rfl

theorem nativeActionJet_pointField (signal : BasePoint → Field289) (point : BasePoint) :
    (nativeActionJet signal point).pointField = nativePoint signal point := rfl

end LowEnergy.SourcePropagationNativeActionHessian
