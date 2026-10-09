import H0mework.Versions.R3bbcbd59.Physics.LowEnergySpectrum.Matrix

/-! Source derivative spectrum, with the original drifting phase removed by translation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
open Evolution Stage9C.Material.SpinPair Polynomial
noncomputable section

def geometricGaugeBlock : Matrix (Fin 4) (Fin 4) ℝ :=
  actualJacobian.submatrix (fun i => i.castLE (by decide)) (fun i => i.castLE (by decide))
def dynamicalBlock : Matrix (Fin 6) (Fin 6) ℝ :=
  actualJacobian.submatrix (fun i => i.castLE (by decide)) (fun i => i.castLE (by decide))
def phaseFeedback : Matrix (Fin 1) (Fin 6) ℝ :=
  actualJacobian.submatrix (fun _ => 6) (fun i => i.castLE (by decide))

private theorem geometricGauge_blocks :
    Matrix.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm geometricGaugeBlock =
      Matrix.fromBlocks geometryBlock 0 0 gaugeBlock := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, Matrix.submatrix, geometricGaugeBlock, actualJacobian_eq,
      geometryBlock_eq, gaugeBlock_eq, finSumFinEquiv]

theorem geometricGauge_characteristic : geometricGaugeBlock.charpoly =
    (X^2+C (648/125:ℝ))*(X^2-C (50/3:ℝ)) := by
  rw [← Matrix.charpoly_reindex (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm,
    geometricGauge_blocks, Matrix.charpoly_fromBlocks_zero₁₂,
    geometry_characteristic, gauge_characteristic]

private theorem dynamical_blocks :
    Matrix.reindex (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).symm
      (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).symm dynamicalBlock =
      Matrix.fromBlocks geometricGaugeBlock 0 0 radialBlock := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, Matrix.submatrix, dynamicalBlock, geometricGaugeBlock,
      actualJacobian_eq, radialBlock_eq, finSumFinEquiv]

theorem dynamical_characteristic : dynamicalBlock.charpoly =
    (X^2+C (648/125:ℝ))*(X^2-C (50/3:ℝ))*(X^2-C (108/125:ℝ)) := by
  rw [← Matrix.charpoly_reindex (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).symm,
    dynamical_blocks, Matrix.charpoly_fromBlocks_zero₁₂,
    geometricGauge_characteristic, radial_characteristic]

private theorem actualJacobian_blocks :
    Matrix.reindex (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm
      (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm actualJacobian =
      Matrix.fromBlocks dynamicalBlock 0 phaseFeedback (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, Matrix.submatrix, dynamicalBlock, phaseFeedback,
      actualJacobian_eq, finSumFinEquiv]

theorem actualJacobian_characteristic : actualJacobian.charpoly =
    X*(X^2+C (648/125:ℝ))*(X^2-C (50/3:ℝ))*(X^2-C (108/125:ℝ)) := by
  rw [← Matrix.charpoly_reindex (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm,
    actualJacobian_blocks, Matrix.charpoly_fromBlocks_zero₁₂,
    dynamical_characteristic, Matrix.charpoly_zero]
  simp
  ring

theorem generator_origin_phase : generator (Evolution.seed 0) = Pi.single 6 frequency := by
  rw [generator_seed]
  funext i
  fin_cases i <;>
    simp [seedVelocity, Contact.Slice.scaleAcceleration, Contact.Slice.impulse,
      Contact.Slice.gaugeAcceleration_zero, Contact.Slice.rate, Contact.Slice.clock_zero, frequency]

theorem generator_phase_translation (x : State) (t : ℝ) :
    generator (x+t • Pi.single 6 frequency) = generator x := by
  funext i
  fin_cases i <;> simp [generator, clock, denominator, gaugeEnergy, contorsion]

theorem background_orbit (time : ℝ) :
    HasDerivAt (fun t : ℝ => Evolution.seed 0+t • Pi.single 6 frequency)
      (generator (Evolution.seed 0+time • Pi.single 6 frequency)) time := by
  rw [generator_phase_translation, generator_origin_phase]
  convert! ((hasDerivAt_id time).smul_const (Pi.single (6 : Fin 7) frequency)).const_add (Evolution.seed 0) using 1
  simp

def corotatingGenerator (x : State) : State := generator x-Pi.single 6 frequency

theorem corotating_origin : corotatingGenerator (Evolution.seed 0) = 0 := by
  rw [corotatingGenerator, generator_origin_phase, sub_self]

theorem corotating_fderiv (v : State) :
    fderiv ℝ corotatingGenerator (Evolution.seed 0) v = linearResponse v := by
  have dg := (generator_contDiffAt (Evolution.seed 0) (seed_admissible 0)).differentiableAt (by simp)
  have derivative := dg.hasFDerivAt.sub_const (Pi.single 6 frequency)
  unfold corotatingGenerator
  rw [derivative.fderiv]
  exact generator_fderiv v

def gaugeGrowthRate : ℝ := Real.sqrt (50/3)
def radialGrowthRate : ℝ := Response.Radial.growthRate
def geometryFrequency : ℝ := Real.sqrt (648/125)

theorem gaugeGrowthRate_positive : 0 < gaugeGrowthRate := Real.sqrt_pos.mpr (by norm_num)
theorem gaugeGrowthRate_squared : gaugeGrowthRate^2 = 50/3 := Real.sq_sqrt (by norm_num)
theorem radialGrowthRate_positive : 0 < radialGrowthRate := Response.Radial.growthRate_pos
theorem radialGrowthRate_squared : radialGrowthRate^2 = 108/125 := Response.Radial.coordinate_rate_sq
theorem geometryFrequency_positive : 0 < geometryFrequency := Real.sqrt_pos.mpr (by norm_num)
theorem geometryFrequency_squared : geometryFrequency^2 = 648/125 := Real.sq_sqrt (by norm_num)

def gaugeEigenvector (rate : ℝ) (i : Fin 7) : ℝ :=
  match i.val with
  | 2 => rate
  | 3 => (50/3)*lapse
  | 6 => (5/2)*lapse
  | _ => 0

def radialEigenvector (rate : ℝ) (i : Fin 7) : ℝ :=
  match i.val with
  | 4 => rate
  | 5 => 2*lapse
  | _ => 0

theorem gauge_eigenvector (rate : ℝ) (square : rate^2 = 50/3) :
    fderiv ℝ generator (Evolution.seed 0) (gaugeEigenvector rate) = rate • gaugeEigenvector rate := by
  rw [generator_fderiv]
  funext i
  fin_cases i <;> simp [linearResponse, gaugeEigenvector, ne_of_gt lapse_pos]
  all_goals nlinarith [square]

theorem radial_eigenvector (rate : ℝ) (square : rate^2 = 108/125) :
    fderiv ℝ generator (Evolution.seed 0) (radialEigenvector rate) = rate • radialEigenvector rate := by
  rw [generator_fderiv]
  funext i
  fin_cases i <;> simp [linearResponse, radialEigenvector]
  all_goals nlinarith [square, lapse_sq]

theorem gauge_growing_mode_nonzero : gaugeEigenvector gaugeGrowthRate ≠ 0 := by
  intro zero
  have component := congrFun zero 2
  exact (ne_of_gt gaugeGrowthRate_positive) component

theorem radial_growing_mode_nonzero : radialEigenvector radialGrowthRate ≠ 0 := by
  intro zero
  have component := congrFun zero 4
  exact (ne_of_gt radialGrowthRate_positive) component

private theorem exponential_linearized (rate : ℝ) (mode : State)
    (eigen : fderiv ℝ generator (Evolution.seed 0) mode = rate • mode) (time : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (rate*t) • mode)
      (fderiv ℝ generator (Evolution.seed 0) (Real.exp (rate*time) • mode)) time := by
  have derivative := (((hasDerivAt_id time).const_mul rate).exp).smul_const mode
  rw [map_smul, eigen, smul_smul]
  convert! derivative using 1
  simp [mul_comm]

theorem gauge_growing_linearized (time : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (gaugeGrowthRate*t) • gaugeEigenvector gaugeGrowthRate)
      (fderiv ℝ generator (Evolution.seed 0)
        (Real.exp (gaugeGrowthRate*time) • gaugeEigenvector gaugeGrowthRate)) time :=
  exponential_linearized _ _ (gauge_eigenvector _ gaugeGrowthRate_squared) time

theorem radial_growing_linearized (time : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (radialGrowthRate*t) • radialEigenvector radialGrowthRate)
      (fderiv ℝ generator (Evolution.seed 0)
        (Real.exp (radialGrowthRate*time) • radialEigenvector radialGrowthRate)) time :=
  exponential_linearized _ _ (radial_eigenvector _ radialGrowthRate_squared) time

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
