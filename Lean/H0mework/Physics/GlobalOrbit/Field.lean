import H0mework.Physics.GlobalOrbit.Phase

/-! Every finite window is a restriction of one completed trajectory. The
already certified whole-field gauge/Dirac consumers apply at every real time. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation Stage9C.Material.SpinPair

noncomputable section

variable {impulse : ℝ}

def CompleteOrbit.slice (trajectory : CompleteOrbit impulse) (time : ℝ) : LocalOrbit (Nonlinear.seed impulse) 0 :=
  trajectory.local (|time|+1) (by positivity)

theorem CompleteOrbit.slice_contains (trajectory : CompleteOrbit impulse) (time : ℝ) :
    time ∈ (trajectory.slice time).window := by
  constructor <;> dsimp [CompleteOrbit.slice, CompleteOrbit.local, LocalOrbit.window] <;>
    linarith [le_abs_self time, neg_abs_le time]

def CompleteOrbit.configuration (trajectory : CompleteOrbit impulse) : StageNineHolonomicConfiguration :=
  (trajectory.local 1 (by norm_num)).configuration

def CompleteOrbit.fieldValue (trajectory : CompleteOrbit impulse) (point : BasePoint) : ℝ :=
  (trajectory.local 1 (by norm_num)).fieldValue point

def CompleteOrbit.helicity (trajectory : CompleteOrbit impulse) (time : ℝ) : ℝ :=
  (trajectory.local 1 (by norm_num)).helicity time

theorem CompleteOrbit.configuration_slice (trajectory : CompleteOrbit impulse) (time : ℝ) :
    trajectory.configuration = (trajectory.slice time).configuration := rfl

theorem CompleteOrbit.gaugeEuler_zero (trajectory : CompleteOrbit impulse) (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 trajectory.configuration point = 0 := by
  rw [trajectory.configuration_slice (point 0)]
  exact (trajectory.slice (point 0)).gaugeEuler_zero point (trajectory.slice_contains (point 0))

theorem CompleteOrbit.primalEuler_zero (trajectory : CompleteOrbit impulse) (point : BasePoint) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField trajectory.configuration point) = 0 := by
  rw [trajectory.configuration_slice (point 0)]
  exact (trajectory.slice (point 0)).primalEuler_zero point (trajectory.slice_contains (point 0))

theorem CompleteOrbit.adjointEuler_zero (trajectory : CompleteOrbit impulse) (point : BasePoint)
    (variation : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource trajectory.configuration variation point = 0 := by
  rw [trajectory.configuration_slice (point 0)]
  exact (trajectory.slice (point 0)).adjointEuler_zero point (trajectory.slice_contains (point 0)) variation

theorem CompleteOrbit.fieldValue_helicity (trajectory : CompleteOrbit impulse) (point : BasePoint) :
    trajectory.fieldValue point = trajectory.helicity (point 0) :=
  (trajectory.slice (point 0)).fieldValue_helicity point (trajectory.slice_contains (point 0))

theorem CompleteOrbit.helicity_eq (trajectory : CompleteOrbit impulse) (time : ℝ) :
    trajectory.helicity time = 3*(trajectory.curve time).1^5 :=
  (trajectory.local 1 (by norm_num)).helicity_eq time

theorem CompleteOrbit.helicity_derivative (trajectory : CompleteOrbit impulse) (time : ℝ) :
    HasDerivAt trajectory.helicity (15*(trajectory.curve time).1^4*((trajectory.curve time).2.1/inertia)) time :=
  (trajectory.slice time).helicity_derivative time (trajectory.slice_contains time)

theorem CompleteOrbit.energy_conserved (trajectory : CompleteOrbit impulse) (time : ℝ) :
    hamiltonian (trajectory.curve time) = hamiltonian (Nonlinear.seed impulse) :=
  (trajectory.slice time).energy_conserved time (trajectory.slice_contains time)

theorem CompleteOrbit.extends_local (trajectory : CompleteOrbit impulse) (time : ℝ)
    (inside : time ∈ (Nonlinear.orbit impulse).window) :
    trajectory.curve time = (Nonlinear.orbit impulse).curve time :=
  (trajectory.slice time).unique_on (Nonlinear.orbit impulse) ⟨trajectory.slice_contains time, inside⟩

theorem CompleteOrbit.zero_recovers (trajectory : CompleteOrbit 0) (time : ℝ) :
    trajectory.curve time = (gaugeScale, 0, frequency*time) :=
  (trajectory.slice time).unique_on (background (|time|+1) (by positivity))
    ⟨trajectory.slice_contains time, trajectory.slice_contains time⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global
