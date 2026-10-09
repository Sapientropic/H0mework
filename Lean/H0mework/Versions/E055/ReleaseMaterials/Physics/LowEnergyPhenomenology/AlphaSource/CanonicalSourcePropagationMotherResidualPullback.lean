import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationPreparedCoupledEuler

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineFormNativeGaugeWedge StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality StageNineConjugateMatterVariation DiracExteriorMatterAction
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
attribute [local irreducible] nativeEuler nativeConfiguration nativePoint nativeLocalAction nativeLocalPoint nativeJetDensity

/-- All nine raw action channels retain their original variational pairings and both independent rotating matter directions. -/
def motherResidualPullback (point : BasePoint) (residual : DiracDualFormNativePointwiseJointResidualCarrier)
    (force : Field289) : ℝ :=
  gravityTopologicalWedgeCoefficient (fieldMultiplier force) residual.gravityMultiplier+
    gravityTopologicalWedgeCoefficient (fieldGravityB force) residual.gravityAuxiliary+
    formNativeP286GaugeWedgeCoefficient (gaugeBInsertion force) residual.p286GaugeAuxiliary+
    lorentzOneFormThreeFormWedgeCoefficient (fieldLorentz force) residual.lorentzConnection+
    p286GaugeOneFormThreeFormWedgeCoefficient (fieldGauge force) residual.p286GaugeConnection+
    residual.scalar (fieldScalar force)+
    residual.matter (matterCoordinateEquiv (diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion force)))+
    residual.conjugateMatter (matterDualCoordinates ((dualInsertion force).comp (diracMatrixMatterAction (ActiveGauge.rotation point))))+
    residual.coframe (fieldCoframe force)

def actualMotherEulerRead (signal : BasePoint→Field289) (point : BasePoint) (force : Field289) : ℝ :=
  motherResidualPullback point (nativeEuler signal point) force

theorem actualMotherEulerRead_original (signal : BasePoint→Field289) (point : BasePoint) (force : Field289) :
    actualMotherEulerRead signal point force=motherResidualPullback point
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource (nativeConfiguration signal) point) force := by
  unfold actualMotherEulerRead
  rw [nativeEuler_original]

/-- The coframe coefficient is differentiated from the original repaired density, rather than supplied as a covector. -/
theorem motherCoframe_direction_generated (signal : BasePoint→Field289) (point : BasePoint)
    (force : Field289) (nondegenerate : Matrix.det (nativePoint signal point).coframe≠0) :
    HasDerivAt (fun a : ℝ=>diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource point (nativePoint signal point)
        ((nativePoint signal point).coframe+a • fieldCoframe force))
      ((nativeEuler signal point).coframe (fieldCoframe force)) 0 := by
  have source:=diracDualFormNativeCoframeLocalDensity_hasFDerivAt positiveSmoothUnifiedSource point (nativePoint signal point) nondegenerate
  have ray : HasDerivAt (fun a : ℝ=>(nativePoint signal point).coframe+a • fieldCoframe force) (fieldCoframe force) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fieldCoframe force)).const_add (nativePoint signal point).coframe
  have generated:=source.comp_hasDerivAt_of_eq (0 : ℝ) ray (by simp)
  convert! generated using 1
  unfold nativeEuler nativeActionJet diracDualFormNativeJointResidualOfActionJet generatedDiracDualFormNativePointwiseActionJet
    nativePoint
  rfl

end LowEnergy.SourcePropagationMotherResidualDirections
