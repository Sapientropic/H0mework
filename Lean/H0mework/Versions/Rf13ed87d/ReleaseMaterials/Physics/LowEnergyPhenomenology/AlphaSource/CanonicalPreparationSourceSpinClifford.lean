import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaussOrderedLoad
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussCoframeSpin

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeSpinReduction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation SU7ExteriorBreakingYukawa
open Stage9C.Material.SpinPair StageNineLorentzConnectionVariation
open PointwiseDiracSpinConnectionLift StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumNoetherChart
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationVacuumMixedFieldReturn
open scoped Topology BigOperators Matrix
local instance : DecidableEq Quantum.Index:=Classical.decEq _

-- The original scalar chart is the same generated chart at both ends.
theorem sourceSpinScalarFrame : generatedScalarFrame positiveSmoothUnifiedSource 0 0=1:=
  generatedTransition_normalized _ _ _

def sourceSpinGamma (e : LorentzianCoframe) (i : LorentzIndex) : DiracMatrix:=
  ∑mu : Fin 4,inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu*
    diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (sourceConnectionBasis i)) mu

private theorem matterAction_smul (c : ℂ) (A : DiracMatrix) :
    diracMatrixMatterAction (c • A)=c • diracMatrixMatterAction A:=by
  apply LinearMap.ext
  intro v
  exact diracMatrixMatterAction_smul_matrix c A v

private theorem matterAction_sum (A : Fin 4→DiracMatrix) :
    diracMatrixMatterAction (∑mu,A mu)=∑mu,diracMatrixMatterAction (A mu):=by
  apply LinearMap.ext
  intro v
  funext a
  change (∑b : Fin 4,(∑mu : Fin 4,A mu a b) • v b)=
    ∑mu : Fin 4,∑b : Fin 4,A mu a b • v b
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]

theorem sourceSpinIncrement_gamma (e : LorentzianCoframe) (i : LorentzIndex) :
    sourceSpinIncrementMother e i=Complex.I • diracMatrixMatterAction (sourceSpinGamma e i):=by
  simp only [sourceSpinIncrementMother,sourceSpinScalarFrame,inv_one,map_one,LinearMap.comp_id]
  rw [sourceSpinGamma,matterAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  exact (diracMatrixMatterAction_mul _ _).symm

theorem sourceSpinVolume (u : JointParameter) (s : ActionState) :
    (generatedVolumeDensity (sourceSpinField u s.1):ℂ)=stateVolume s:=by
  rfl

theorem sourceInverseMomentumMatrix (s : ActionState) :
    Quantum.operatorMatrix (inverseMomentumMother s)=statePhase s:=
  Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _

def sourceGaussSpinClifford (z : SourceCoordinateSlice) (i : LorentzIndex) : DiracMatrix:=
  (-Complex.I*(lapse:ℂ)) •
    (diracGammaZero*sourceSpinGamma (sourceGaussCoframe z) i)

theorem sourceGaussSpinClifford_original (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    sourceSpinMatrix (f,z.val) (sourceState z.val) i=
      GaussCoframeSpin.spinLift (sourceGaussSpinClifford z.val i):=by
  rw [sourceSpinMatrix,sourceSpinVolume,sourceSpinMomentumMother,Quantum.matrix_composition,
    sourceInverseMomentumMatrix,sourceSpinIncrement_gamma,map_smul]
  rw [statePhase]
  have inverse : Ring.inverse (principalMatrix (sourceState z.val).1)=
      Quantum.operatorMatrix (StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipalInverse
        (sourceState z.val).1):=
    principal_inverse_original _ (CanonicalGradedSpatialSource.temporal_noncharacteristic z)
  have temporal : StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipalInverse
      (sourceState z.val).1=((lapse:ℂ)*Complex.I) • diracMatrixMatterAction diracGammaZero:=
    CanonicalGradedSpatialSource.temporal_inverse z
  rw [inverse,temporal,map_smul]
  have volume : stateVolume (sourceState z.val)≠0:=by
    unfold stateVolume
    exact_mod_cast (abs_ne_zero.mpr (coframe_nondegenerate z))
  rw [←GaussCoframeSpin.spinLift_source]
  change _=Quantum.operatorMatrix (diracMatrixMatterAction (sourceGaussSpinClifford z.val i))
  rw [sourceGaussSpinClifford,matterAction_smul,map_smul,diracMatrixMatterAction_mul,
    Quantum.matrix_composition]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  field_simp [volume]
  simp only [Complex.I_sq]
  ring

end LowEnergy.PreparationVacuumCoframeSpinReduction
