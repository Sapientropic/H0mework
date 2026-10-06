import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherPreparedContact
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualOrderedTimeDrive

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNoetherTime
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumNoetherChart PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection
open FullQuantum.StateGreen
open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] inversePhase statePhase momentumFirst phaseVariation
  rawMomentumMatrix rawMomentumInverse rawMomentumConnection

/-- This is the original raw momentum, expressed on the actual 289 real field directions. -/
def rawMomentumVariationMap (s : ActionState) : Field289→L[ℝ] SourceMatrix:=
  ((ContinuousLinearMap.mul ℂ SourceMatrix densityActionMatrix).restrictScalars ℝ).comp
    ((fderiv ℝ inversePhase s).comp fieldDirectionLinear.toContinuousLinearMap)

theorem rawMomentumVariationMap_actual (s : ActionState) (force : Field289) :
    rawMomentumVariationMap s force=densityActionMatrix*momentumFirst force s:=by
  unfold rawMomentumVariationMap momentumFirst
  rfl

theorem rawMomentumVariation_generated (s : ActionState) (valid : s∈validStates) (force : Field289) :
    HasDerivAt (fun r : ℝ=>rawMomentumMatrix (s+r • fieldDirection force))
      (rawMomentumVariationMap s force) 0:=by
  have actual:=(momentumFirst_generated force s valid).const_mul densityActionMatrix
  unfold rawMomentumMatrix
  rw [rawMomentumVariationMap_actual]
  exact actual

/-- Relative time variation retains the noncommuting D-conjugation. -/
def rawTimeConnection (s : ActionState) (velocity : Field289) : SourceMatrix:=
  rawMomentumVariationMap s velocity*rawMomentumInverse s

theorem rawTimeConnection_original (s : ActionState) (velocity : Field289) :
    rawTimeConnection s velocity=rawMomentumConnection velocity s:=by
  rw [rawTimeConnection,rawMomentumVariationMap_actual]
  unfold rawMomentumInverse rawMomentumConnection
  simp only [mul_assoc]

def rawInverseVariation (s : ActionState) (force : Field289) : SourceMatrix:=
  -(rawMomentumInverse s*rawMomentumVariationMap s force*rawMomentumInverse s)

theorem rawInverseVariation_generated (s : ActionState) (valid : s∈validStates) (force : Field289) :
    HasDerivAt (fun r : ℝ=>rawMomentumInverse (s+r • fieldDirection force))
      (rawInverseVariation s force) 0:=by
  have actual:=(inverseMomentumFirst_generated force s valid).mul_const densityActionInverse
  have algebra : phaseVariation force s*densityActionInverse=rawInverseVariation s force:=by
    rw [momentumFirst_inverse force s valid,rawInverseVariation,rawMomentumVariationMap_actual]
    unfold rawMomentumInverse
    simp only [mul_assoc,neg_mul,mul_neg]
    rw [←mul_assoc densityActionInverse densityActionMatrix,densityAction_two_sided.2,one_mul]
  unfold rawMomentumInverse
  exact actual.congr_deriv algebra

theorem momentumVariation_time_generated (s : ActionState) (signal : ℝ→SourceJet Field289)
    (t : ℝ) (paid : HasSourceJets signal t) :
    HasDerivAt (fun r=>rawMomentumVariationMap s (signal r).value)
      (rawMomentumVariationMap s (signal t).first) t:=
  (rawMomentumVariationMap s).hasFDerivAt.comp_hasDerivAt t paid.1

theorem momentumTimeConnection_generated (s : ActionState) (signal : ℝ→SourceJet Field289)
    (t : ℝ) (paid : HasSourceJets signal t) :
    HasDerivAt (fun r=>rawTimeConnection s (signal r).value)
      (rawTimeConnection s (signal t).first) t:=
  (momentumVariation_time_generated s signal t paid).mul_const (rawMomentumInverse s)

theorem inverseMomentum_time_generated (s : ActionState) (signal : ℝ→SourceJet Field289)
    (t : ℝ) (paid : HasSourceJets signal t) :
    HasDerivAt (fun r=>rawInverseVariation s (signal r).value)
      (rawInverseVariation s (signal t).first) t:=
  (((momentumVariation_time_generated s signal t paid).const_mul (rawMomentumInverse s)).mul_const
    (rawMomentumInverse s)).neg

end LowEnergy.SourcePropagationNoetherTime
