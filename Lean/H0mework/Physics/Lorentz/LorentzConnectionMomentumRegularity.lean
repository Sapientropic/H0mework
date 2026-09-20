import H0mework.Physics.Lorentz.LorentzConnectionWeakEquation
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# S9-C3b4a: smooth Lorentz connection BF momentum

The coefficient of the derivative of a compact Lorentz connection variation
is expressed through the same-coframe polynomial intertwiner already proved
for the gravity auxiliary equation.  The dynamic inverse coframe therefore
cancels before regularity is established.

Smoothness of the BF differential momentum is generated from the primitive
coframe and gravity auxiliary fields.  It is not accepted as a regularity,
current, or equation receipt.  This is the analytic input for genuine
compact-support integration by parts in C3b4b.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzConnectionMomentumRegularity

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActionVariation
open scoped ContDiff

noncomputable section

set_option maxHeartbeats 600000

theorem holonomicGravityAuxiliary_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.gravityAuxiliary := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  exact smooth.2.2.1 internalPair spacetimePair

theorem holonomicGravityCoframeTwoFormLinear_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (bivector : BasePoint → PhysicalBivector)
    (bivectorSmooth : ContDiff ℝ ∞ bivector) :
    ContDiff ℝ ∞ fun point =>
      fun internalPair =>
        coframeTwoFormLinear (configuration.coframe point)
          (bivector point internalPair) := by
  apply contDiff_pi'
  intro internalPair
  exact coframeTwoFormLinear_apply_contDiff configuration.coframe
    (holonomicCoframe_contDiff configuration smooth)
    (fun point => bivector point internalPair)
    (contDiff_pi.mp bivectorSmooth internalPair)

theorem holonomicGravityFixedHodge_apply_contDiff
    (bivector : BasePoint → PhysicalBivector)
    (bivectorSmooth : ContDiff ℝ ∞ bivector) :
    ContDiff ℝ ∞ fun point =>
      fun internalPair => lorentzianCoframeHodge
        (bivector point internalPair) := by
  apply contDiff_pi'
  intro internalPair
  exact lorentzianCoframeHodge_apply_contDiff
    (fun point => bivector point internalPair)
    (contDiff_pi.mp bivectorSmooth internalPair)

/-- The coefficient paired with one constant physical-bivector curvature
direction after the dynamic Hodge has been polynomialized. -/
def lorentzConnectionBFDifferentialMomentum
    (configuration : StageNineHolonomicConfiguration)
    (direction : PhysicalBivector) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    gravityAuxiliaryHodgePairingPolynomial
      (configuration.coframe point)
      (configuration.gravityAuxiliary point) direction

theorem lorentzConnectionBFDifferentialMomentum_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : PhysicalBivector) :
    ContDiff ℝ ∞
      (lorentzConnectionBFDifferentialMomentum configuration direction) := by
  have coframeSmooth := holonomicCoframe_contDiff configuration smooth
  have auxiliarySmooth := holonomicGravityAuxiliary_contDiff configuration
    smooth
  have auxiliaryTransformSmooth :=
    holonomicGravityCoframeTwoFormLinear_apply_contDiff configuration smooth
      configuration.gravityAuxiliary auxiliarySmooth
  have directionTransformSmooth :=
    holonomicGravityCoframeTwoFormLinear_apply_contDiff configuration smooth
      (fun _ => direction) contDiff_const
  have hodgeDirectionTransformSmooth :=
    holonomicGravityFixedHodge_apply_contDiff
      (fun point => fun internalPair =>
        coframeTwoFormLinear (configuration.coframe point)
          (direction internalPair)) directionTransformSmooth
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff configuration
    smooth nondegenerate
  unfold lorentzConnectionBFDifferentialMomentum
    gravityAuxiliaryHodgePairingPolynomial
  apply volumeSmooth.mul
  apply ContDiff.sum
  intro internalPair _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro spacetimePair _
  exact (contDiff_const.mul
      (contDiff_pi.mp (contDiff_pi.mp auxiliaryTransformSmooth internalPair)
        spacetimePair)).mul
    (contDiff_pi.mp (contDiff_pi.mp hodgeDirectionTransformSmooth internalPair)
      spacetimePair)

theorem lorentzConnectionBFDifferentialMomentum_eq_density
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (direction : PhysicalBivector) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum configuration direction point =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        gravityBFCurvatureIncrementDensity
          (configuration.coframe point)
          (configuration.gravityAuxiliary point) direction := by
  unfold lorentzConnectionBFDifferentialMomentum
    gravityBFCurvatureIncrementDensity
  rw [gravityAuxiliaryHodgePairingPolynomial_eq
    (configuration.coframe point) (nondegenerate point)]

end

end SaturationMonoid.PhysicsCore.StageNineLorentzConnectionMomentumRegularity
