import H0mework.Versions.R2.Physics.RadialDynamics.Jacobi

/-! The original independent Dirac dual follows the radial phase. Its
current is unchanged by that phase evolution, while its kinetic jet responds. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open StageNineMatterVariation StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionVariationDensity StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeAuxiliaryVariation
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair

noncomputable section

def unitPhase (angle : ℝ) : ℂ := Complex.exp ((angle : ℂ)*Complex.I)

theorem unitPhase_opposite (angle : ℝ) : unitPhase angle*unitPhase (-angle) = 1 := by
  unfold unitPhase
  rw [← Complex.exp_add]
  simp

theorem unitPhase_hasDerivAt (angle : ℝ) :
    HasDerivAt unitPhase (Complex.I*unitPhase angle) angle := by
  convert (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp using 1
  all_goals first | rfl | simp [unitPhase]; ring

def movingMatter (angle : ℝ) : DiracExteriorMatterCarrier :=
  spinPairMatter (unitPhase angle) (unitPhase (-angle))

def movingDual (angle : ℝ) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  spinPairDual ((spinScale : ℂ)*unitPhase angle) ((spinScale : ℂ)*unitPhase (-angle))

theorem movingCurrent (angle : ℝ) (axis : Fin 3) (probe : P286LieBlockData) :
    (spinPairCurrentComplex axis.succ probe ((spinScale : ℂ)*unitPhase angle)
      ((spinScale : ℂ)*unitPhase (-angle)) (unitPhase angle) (unitPhase (-angle))).re =
      4*spinScale*p286LiePairing (sourceColorP286Generator axis) probe := by
  have product : (spinScale : ℂ)*unitPhase angle*unitPhase (-angle) +
      (spinScale : ℂ)*unitPhase (-angle)*unitPhase angle = (2*spinScale : ℝ) := by
    rw [mul_assoc, unitPhase_opposite]
    rw [mul_assoc, mul_comm (unitPhase (-angle)), unitPhase_opposite]
    push_cast
    ring
  rw [spinPairCurrentComplex_spatial_pairing _ _ _ _ _ _ _ product]
  ring

def temporalMatter (rate angle : ℝ) : DiracExteriorMatterCarrier :=
  spinPairMatter (Complex.I*(rate : ℂ)*unitPhase angle)
    (-Complex.I*(rate : ℂ)*unitPhase (-angle))

def spatialMatter (amplitude angle : ℝ) (axis : Fin 3) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift (homogeneousConnection spinScale) axis.succ)
      (movingMatter angle) +
    diracExteriorMotherLieAction (p286LieBlockEmbed (amplitude • sourceColorP286Generator axis))
      (movingMatter angle)

def matterJet (amplitude rate angle : ℝ) : StageNineContinuumPointField :=
  { toContinuumPointField Runtime.configuration 0 with
    coframe := homogeneousCoframe lapse
    matter := movingMatter angle
    conjugateMatter := movingDual angle
    matterCovariantDerivative := ![temporalMatter rate angle, spatialMatter amplitude angle 0,
      spatialMatter amplitude angle 1, spatialMatter amplitude angle 2] }

theorem temporalKinetic (rate angle : ℝ) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := homogeneousCoframe lapse, derivative := 0 } 0)
      (temporalMatter rate angle) =
      ((rate : ℂ)/(lapse : ℂ)) • spinPairMatter (unitPhase (-angle)) (unitPhase angle) := by
  rw [homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm, temporalMatter, spinPair_temporalKinetic, smul_smul]
  congr 1
  push_cast
  ring

theorem kineticVector_eq (amplitude rate angle : ℝ) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0 (matterJet amplitude rate angle) =
      (((rate : ℂ)/(lapse : ℂ)) - 3*((spinScale-amplitude : ℝ) : ℂ)/2) •
        spinPairMatter (unitPhase (-angle)) (unitPhase angle) := by
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, matterJet]
  rw [Finset.smul_sum, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]
  rw [temporalKinetic]
  have spatial (axis : Fin 3) :
      Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := homogeneousCoframe lapse, derivative := 0 } axis.succ)
        (spatialMatter amplitude angle axis) =
      (-((spinScale-amplitude : ℝ) : ℂ)/2) • spinPairMatter (unitPhase (-angle)) (unitPhase angle) := by
    rw [homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
    simp only [Fin.succ_ne_zero, ite_false, one_smul]
    exact spinPair_spatialKinetic spinScale amplitude axis _ _
  have first := spatial 0
  have second := spatial 1
  have third := spatial 2
  rw [show (0 : Fin 3).succ = (1 : Fin 4) by decide] at first
  rw [show (1 : Fin 3).succ = (2 : Fin 4) by decide] at second
  rw [show (2 : Fin 3).succ = (3 : Fin 4) by decide] at third
  simp only [Function.comp_apply, Matrix.cons_val_succ, Matrix.cons_val_zero]
  rw [first, second, third]
  module

theorem kineticVector_closed (amplitude angle : ℝ) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0
      (matterJet amplitude (3*lapse/2*(spinScale-amplitude)) angle) = 0 := by
  rw [kineticVector_eq]
  have coefficient : (((3*lapse/2*(spinScale-amplitude) : ℝ) : ℂ)/(lapse : ℂ)) -
      3*((spinScale-amplitude : ℝ) : ℂ)/2 = 0 := by
    push_cast
    field_simp [show (lapse : ℂ) ≠ 0 by exact_mod_cast ne_of_gt lapse_pos]
    ring
  rw [coefficient, zero_smul]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
