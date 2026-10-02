import H0mework.Versions.R2.Physics.RadialDynamics.Profile

/-! Canonical radial mechanics from the gauge density and its actual charged
first coefficient. Coframe and spin are fixed at the original background. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra Stage9C.Material.SpinPair

noncomputable section

def sourceLoad : ℝ := formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 0
  (toContinuumPointField Runtime.configuration 0)
  (fun direction => p286CoordinateEquiv (gaugePotential 1 direction))

theorem sourceLoad_eq : sourceLoad = 6*lapse*spinScale := by
  unfold sourceLoad
  rw [Runtime.configuration_eq, actual_chargedCoefficient]
  have pairing (axis : Fin 3) : p286LiePairing (sourceColorP286Generator axis)
      (p286CoordinateEquiv.symm (p286CoordinateEquiv (gaugePotential 1 axis.succ))) = 1/2 := by
    rw [LinearEquiv.symm_apply_apply]
    have same : gaugePotential 1 axis.succ = sourceColorP286Generator axis := by
      fin_cases axis <;> simp [gaugePotential]
    rw [same]
    exact (sourceColor_pairing axis axis).trans (if_pos rfl)
  simp_rw [pairing]
  simp
  ring

def lagrangian (amplitude velocity : ℝ) : ℝ :=
  gaugeLagrangian amplitude velocity + sourceLoad*amplitude

def momentum (amplitude velocity : ℝ) : ℝ := deriv (lagrangian amplitude) velocity
def inertia : ℝ := deriv (momentum gaugeScale) 0
def potential (amplitude : ℝ) : ℝ := -lagrangian amplitude 0
def restoring (amplitude : ℝ) : ℝ := deriv potential amplitude
def stiffness : ℝ := deriv restoring gaugeScale

theorem lagrangian_hasDerivAt_velocity (amplitude velocity : ℝ) :
    HasDerivAt (lagrangian amplitude) (3*lapse/(2*sourceCoupling)*velocity) velocity := by
  unfold lagrangian
  simp_rw [gaugeLagrangian_eq]
  convert (((hasDerivAt_id velocity).pow 2).const_mul (3*lapse/(4*sourceCoupling))).sub_const
    (3/(4*sourceCoupling*lapse)*amplitude^4) |>.add_const (sourceLoad*amplitude) using 1
  all_goals first | rfl | simp only [id_eq, Nat.cast_ofNat]; ring

theorem momentum_eq (amplitude velocity : ℝ) :
    momentum amplitude velocity = 3*lapse/(2*sourceCoupling)*velocity :=
  (lagrangian_hasDerivAt_velocity amplitude velocity).deriv

theorem inertia_eq : inertia = 3*lapse/(2*sourceCoupling) := by
  unfold inertia
  rw [show momentum gaugeScale = fun velocity => 3*lapse/(2*sourceCoupling)*velocity from
    funext (momentum_eq gaugeScale)]
  simp

theorem inertia_pos : 0 < inertia := by
  rw [inertia_eq, sourceCoupling_eq]
  exact div_pos (mul_pos (by norm_num) lapse_pos) (by norm_num)

theorem potential_eq (amplitude : ℝ) :
    potential amplitude = 3/(4*sourceCoupling*lapse)*amplitude^4 - 6*lapse*spinScale*amplitude := by
  simp [potential, lagrangian, gaugeLagrangian_eq, sourceLoad_eq]
  ring

theorem potential_hasDerivAt (amplitude : ℝ) :
    HasDerivAt potential
      (3/(sourceCoupling*lapse)*amplitude^3 - 6*lapse*spinScale) amplitude := by
  simp_rw [show potential = fun r => 3/(4*sourceCoupling*lapse)*r^4 - 6*lapse*spinScale*r from
    funext potential_eq]
  convert (((hasDerivAt_id amplitude).pow 4).const_mul (3/(4*sourceCoupling*lapse))).sub
    ((hasDerivAt_id amplitude).const_mul (6*lapse*spinScale)) using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem restoring_eq (amplitude : ℝ) :
    restoring amplitude = 3/(sourceCoupling*lapse)*amplitude^3 - 6*lapse*spinScale :=
  (potential_hasDerivAt amplitude).deriv

theorem stiffness_eq : stiffness = 9*gaugeScale^2/(sourceCoupling*lapse) := by
  unfold stiffness
  rw [show restoring = fun amplitude => 3/(sourceCoupling*lapse)*amplitude^3 - 6*lapse*spinScale from
    funext restoring_eq]
  convert ((((hasDerivAt_id gaugeScale).pow 3).const_mul (3/(sourceCoupling*lapse))).sub_const
    (6*lapse*spinScale)).deriv using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem stiffness_pos : 0 < stiffness := by
  rw [stiffness_eq, sourceCoupling_eq]
  exact div_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 2)) (mul_pos (by norm_num) lapse_pos)

theorem euler_action (amplitude acceleration : ℝ) :
    inertia*acceleration + restoring amplitude = (3/2:ℝ)*force amplitude acceleration := by
  rw [inertia_eq, restoring_eq]
  unfold force
  ring

theorem equilibrium : restoring gaugeScale = 0 := by
  simpa using euler_action gaugeScale 0 |>.trans (by rw [force_background]; ring)

def energy (amplitude canonicalMomentum : ℝ) : ℝ :=
  canonicalMomentum*(canonicalMomentum/inertia) - lagrangian amplitude (canonicalMomentum/inertia)

theorem energy_eq (amplitude canonicalMomentum : ℝ) :
    energy amplitude canonicalMomentum = canonicalMomentum^2/(2*inertia) + potential amplitude := by
  have coeff : 3*lapse/(4*sourceCoupling) = inertia/2 := by rw [inertia_eq]; ring
  unfold energy lagrangian
  rw [gaugeLagrangian_eq, potential_eq, sourceLoad_eq, coeff]
  field_simp [ne_of_gt inertia_pos, ne_of_gt lapse_pos, sourceCoupling_eq]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
