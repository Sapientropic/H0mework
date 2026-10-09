import H0mework.Physics.LowEnergy.BosonCausal.Response
import H0mework.Versions.R3bbcbd59.Physics.LowEnergySpectrum.Matrix

/-! The forced state uses the actual derivative of the original homogeneous
generator; the two unforced radial coordinates are removed by restriction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory Stage9C.Material.SpinPair
open scoped Matrix
noncomputable section

def retained (i : Fin 5) : Fin 7 := ![0,1,2,3,6] i
def sourceJacobian : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => Spectrum.actualJacobian (retained i) (retained j)

theorem sourceJacobian_original : sourceJacobian =
    !![0,(lapse : ℂ),0,0,0;
       -12*(lapse : ℂ),0,0,0,0;
       0,0,0,1/(lapse : ℂ),0;
       0,0,(50/3)*(lapse : ℂ),0,0;
       -3*(lapse : ℂ)*(spinScale : ℂ),0,(5/2)*(lapse : ℂ),0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceJacobian,retained,Spectrum.actualJacobian_eq]

def sourceForce : Fin 5 → ℂ :=
  ![0,18/125,0,24*(spinScale : ℂ)/25,18*(spinScale : ℂ)/125]

def geometricPosition (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  (lapse : ℂ)*(18/125)*pairForced (Complex.I*(oscillation : ℂ)) source t
def geometricVelocity (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  (18/125)*pairVelocity (Complex.I*(oscillation : ℂ)) source t
def gaugePosition (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  (24*(spinScale : ℂ)/25)/(lapse : ℂ)*pairForced (growth : ℂ) source t
def gaugeVelocity (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  (24*(spinScale : ℂ)/25)*pairVelocity (growth : ℂ) source t
def phaseForce (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  -3*(lapse : ℂ)*(spinScale : ℂ)*geometricPosition source t+
    (5/2)*(lapse : ℂ)*gaugePosition source t+(18*(spinScale : ℂ)/125)*source t
def phaseResponse (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ in (0 : ℝ)..t, phaseForce source s
def sourceState (source : ℝ → ℂ) (t : ℝ) : Fin 5 → ℂ :=
  ![geometricPosition source t,geometricVelocity source t,
    gaugePosition source t,gaugeVelocity source t,phaseResponse source t]

theorem geometric_derivative (source : ℝ → ℂ) (regular : Continuous source) (t : ℝ) :
    HasDerivAt (geometricPosition source) ((lapse : ℂ)*geometricVelocity source t) t ∧
    HasDerivAt (geometricVelocity source)
      (-12*(lapse : ℂ)*geometricPosition source t+(18/125)*source t) t := by
  obtain ⟨position,velocity,_,_⟩ := responseTo_generated_second_order source regular t
  constructor
  · convert! position.const_mul ((lapse : ℂ)*(18/125)) using 1
    simp only [geometricVelocity]
    ring
  · convert! velocity.const_mul (18/125 : ℂ) using 1
    have square : (lapse : ℂ)^2=(54/125 : ℂ) := by
      rw [← Complex.ofReal_pow,lapse_sq]; norm_num
    unfold geometricPosition
    linear_combination -216/125*pairForced (Complex.I*(oscillation : ℂ)) source t*square

theorem gauge_derivative (source : ℝ → ℂ) (regular : Continuous source) (t : ℝ) :
    HasDerivAt (gaugePosition source) (gaugeVelocity source t/(lapse : ℂ)) t ∧
    HasDerivAt (gaugeVelocity source)
      ((50/3)*(lapse : ℂ)*gaugePosition source t+(24*(spinScale : ℂ)/25)*source t) t := by
  obtain ⟨_,_,position,velocity⟩ := responseTo_generated_second_order source regular t
  have nonzero : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  constructor
  · convert! position.const_mul ((24*(spinScale : ℂ)/25)/(lapse : ℂ)) using 1
    simp only [gaugeVelocity]
    ring
  · convert! velocity.const_mul (24*(spinScale : ℂ)/25) using 1
    unfold gaugePosition
    field_simp [nonzero]

theorem phase_derivative (source : ℝ → ℂ) (regular : Continuous source) (t : ℝ) :
    HasDerivAt (phaseResponse source) (phaseForce source t) t := by
  have cg : Continuous (geometricPosition source) :=
    continuous_iff_continuousAt.mpr fun t => (geometric_derivative source regular t).1.continuousAt
  have ca : Continuous (gaugePosition source) :=
    continuous_iff_continuousAt.mpr fun t => (gauge_derivative source regular t).1.continuousAt
  have continuousForce : Continuous (phaseForce source) := by unfold phaseForce; fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (continuousForce.intervalIntegrable (μ := volume) 0 t)
    continuousForce.aestronglyMeasurable.stronglyMeasurableAtFilter continuousForce.continuousAt

theorem sourceState_initial (source : ℝ → ℂ) : sourceState source 0=0 := by
  ext i
  fin_cases i <;> simp [sourceState,geometricPosition,geometricVelocity,gaugePosition,
    gaugeVelocity,phaseResponse,pairForced,pairVelocity,forcedMode_zero]

theorem sourceState_original_ode (source : ℝ → ℂ) (regular : Continuous source) (t : ℝ) :
    HasDerivAt (sourceState source)
      (sourceJacobian*ᵥsourceState source t+source t • sourceForce) t := by
  obtain ⟨dg,dh⟩ := geometric_derivative source regular t
  obtain ⟨da,db⟩ := gauge_derivative source regular t
  have dp := phase_derivative source regular t
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  all_goals simp [sourceState,sourceJacobian_original,sourceForce]
  · simpa only [mul_comm] using dg
  · convert! dh using 1
    ring
  · exact da
  · convert! db using 1
    ring
  · convert! dp using 1
    simp only [phaseForce]
    ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
