import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Physical
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Gain
open Collision Quantum Resource Propagation.Interface Propagation.Producer Load.Source
open Load.Producer.StrictThermal Blocks Blocks.EnergyFrame Inverse.Scaled.Finite
open Replenish Replenish.Physical
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem energy_upper_from_ground {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (positive : rho.PosSemidef)
    (upper groundBound : ℝ) (bounded : ∀ i, hH.eigenvalues i ≤ upper)
    (groundBounded : hH.eigenvalues Spectrum.lastIndex ≤ groundBound) :
    energy H rho ≤ upper*rho.trace.re-(upper-groundBound)*energy (Spectrum.spectralPure H hH Spectrum.lastIndex) rho := by
  let A := conjugation (star hH.eigenvectorUnitary) rho
  have hA : A.PosSemidef := conjugation_posSemidef _ _ positive
  have mass : ∑ i, (A i i).re=rho.trace.re := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum] using congrArg Complex.re (conjugation_trace (star hH.eigenvectorUnitary) rho)
  have read : energy H rho=∑ i, hH.eigenvalues i*(A i i).re := by
    rw [← Work.Capacity.energy_unitary_conjugation H rho (star hH.eigenvectorUnitary),
      hH.conjStarAlgAut_star_eigenvectorUnitary]
    change energy (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) A=_
    simp [energy,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Complex.mul_re]
  have ground : energy (Spectrum.spectralPure H hH Spectrum.lastIndex) rho=
      (A Spectrum.lastIndex Spectrum.lastIndex).re := by
    have pulled := energy_pullback (Spectrum.basisPure (Spectrum.lastIndex (ι := ι))) rho (star hH.eigenvectorUnitary)
    simp only [star_star] at pulled
    change energy (Spectrum.basisPure Spectrum.lastIndex) A=
      energy (Spectrum.spectralPure H hH Spectrum.lastIndex) rho at pulled
    rw [← pulled]
    simp [energy,Spectrum.basisPure,Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  rw [read,ground]
  calc
    _ ≤ ∑ i, (upper-(if i=Spectrum.lastIndex then upper-groundBound else 0))*(A i i).re := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1
      by_cases same : i=Spectrum.lastIndex
      · subst i; simpa using groundBounded
      · simpa only [same,ite_false,sub_zero] using bounded i
    _ = _ := by
      simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,mass,ite_mul,zero_mul]
      simp

theorem right_pc_upper : pcEnergyOf (suppliedBlock Replenish.origin) ≤
    (93/10 : ℝ)*(suppliedBlock Replenish.origin).trace.re-(476/10 : ℝ)*energy groundProjector (pcMatrixOf (suppliedBlock Replenish.origin)) := by
  have positive := Collision.systemReduce_posSemidef _
    (Powered.Dynamics.systemReduce_posSemidef _ (suppliedBlock_positive Replenish.origin))
  have bound := energy_upper_from_ground Powered.Producer.poweredTotalHamiltonian
    (pcMatrixOf (suppliedBlock Replenish.origin)) Powered.Producer.poweredTotalHamiltonian_hermitian positive
    (93/10) (-(383/10)) (fun i => (Spectrum.eigenvalue_le_first _ _ i).trans Replenish.Bounds.powered_top_upper.le)
      Replenish.Bounds.powered_ground_upper.le
  rw [pcMatrixOf,Collision.systemReduce_trace,Powered.Dynamics.systemReduce_trace] at bound
  rw [show (93/10 : ℝ)-(-(383/10))=476/10 by norm_num] at bound
  exact bound

theorem source_gap_lower : (24/25 : ℝ) < gap := by
  have donor := current_right_donor_lower
  have ground := current_right_ground_lower
  have mass := origin_pointer_upper
  rw [← suppliedBlock_mass] at mass
  unfold gap
  linarith only [donor,ground,mass,right_pc_upper]

theorem source_transfer_positive : (3/4 : ℝ) < Registered.transfer := by
  have massPositive : 0 ≤ (suppliedBlock Replenish.origin).trace.re :=
    (Complex.nonneg_iff.mp (suppliedBlock_positive Replenish.origin).trace_nonneg).1
  have massUpper : (suppliedBlock Replenish.origin).trace.re ≤ 1 := by
    rw [suppliedBlock_mass]
    exact origin_pointer_upper.le.trans (by norm_num : (250001/500000 : ℝ) ≤ 1)
  have error : 4*‖Powered.Producer.poweredTotalHamiltonian‖*(nativeClockStep : ℝ)*(suppliedBlock Replenish.origin).trace.re ≤ (18/100 : ℝ) := calc
    _ ≤ (4 : ℝ)*90*(1/2000)*1 := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left Inverse.original_PC_norm (by norm_num))
        nativeClock_small.2.le nativeClock_small.1.le (by norm_num)) massUpper massPositive (by norm_num)
    _ = _ := by norm_num
  linarith only [Registered.source_transfer_lower,source_gap_lower,error]

private theorem energy_pulled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    energy O (conjugation U rho)=energy (conjugation (star U) O) rho := energy_pullback _ _ _

theorem load_error (rho : Current.FullJoint) (positive : rho.PosSemidef) :
    |pcEnergyOf (conjugation (Current.loadPulse (nativeClockStep : ℝ)) rho)-pcEnergyOf rho| ≤
      (101 : ℝ)*(nativeClockStep : ℝ)*rho.trace.re := by
  have read (r : Current.FullJoint) : energy Sectors.pcObservable r=pcEnergyOf r := Population.pc_lift_energy _ _
  rw [← read _,← read _,energy_pulled,← Load.Producer.HeatProbability.energy_sub_left]
  have bound := Blocks.energy_norm_mass
    (conjugation (star (Current.loadPulse (nativeClockStep : ℝ))) Sectors.pcObservable-Sectors.pcObservable) rho positive
  have operator := Inverse.original_body_load_response (nativeClockStep : ℝ)
  change ‖conjugation (star (Current.loadPulse (nativeClockStep : ℝ))) Sectors.pcObservable-Sectors.pcObservable‖ ≤
    |(nativeClockStep : ℝ)| *Inverse.loadResponseCost at operator
  rw [abs_of_pos nativeClock_small.1] at operator
  have opBound : ‖conjugation (star (Current.loadPulse (nativeClockStep : ℝ))) Sectors.pcObservable-Sectors.pcObservable‖ ≤
      (101 : ℝ)*(nativeClockStep : ℝ) := operator.trans (by nlinarith only [Inverse.original_load_cost,nativeClock_small.1])
  exact bound.trans (mul_le_mul_of_nonneg_right opBound (Complex.nonneg_iff.mp positive.trace_nonneg).1)

private theorem body_trace {ι : Type*} [Fintype ι] (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (bodyRead rho).trace=rho.trace := by
  rw [bodyRead,Matrix.trace_add]
  have h := trace_fromBlocks rho.toBlocks₁₁ rho.toBlocks₁₂ rho.toBlocks₂₁ rho.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at h
  exact h.symm

theorem left_mass_le_one (current : Live.State) : (loadBlock current).trace.re ≤ 1 := by
  have total := congrArg Complex.re ((body_trace current.joint).trans current.normalized)
  rw [body_blocks,Matrix.trace_add,Complex.add_re,Complex.one_re] at total
  have right := (Complex.nonneg_iff.mp (suppliedBlock_positive current).trace_nonneg).1
  linarith only [total,right]

def firstLoad : ℝ := pcEnergyOf (loadBlock Registered.target)-pcEnergyOf (loadBlock Replenish.origin)
def secondLoad : ℝ := pcEnergyOf (bodyRead Registered.execution.joint)-pcEnergyOf (bodyRead Registered.target.joint)

theorem first_load_error : |firstLoad| ≤ (101/2000 : ℝ) := by
  unfold firstLoad Registered.target
  rw [loadBlock_next]
  have bound := load_error (loadBlock Replenish.origin) (loadBlock_positive Replenish.origin)
  have pos := (Complex.nonneg_iff.mp (loadBlock_positive Replenish.origin).trace_nonneg).1
  apply bound.trans
  calc
    _ ≤ (101 : ℝ)*(1/2000)*1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left nativeClock_small.2.le (by norm_num))
        (left_mass_le_one Replenish.origin) pos (by norm_num)
    _ = _ := by norm_num

theorem second_load_error : |secondLoad| ≤ (101/2000 : ℝ) := by
  unfold secondLoad Registered.execution
  rw [Live.loadNext_body]
  have positive : (bodyRead Registered.target.joint).PosSemidef :=
    (Registered.target.positive.submatrix Sum.inl).add (Registered.target.positive.submatrix Sum.inr)
  have bound := load_error (bodyRead Registered.target.joint) positive
  rw [body_trace,Registered.target.normalized,Complex.one_re,mul_one] at bound
  exact bound.trans (by nlinarith only [nativeClock_small.2])

theorem net_gain_split : Registered.netGain=Registered.transfer+firstLoad+secondLoad := by
  have split := response_pc_account Replenish.origin
  change pcEnergyOf (bodyRead Registered.target.joint)-pcEnergyOf (bodyRead Replenish.origin.joint)=
    firstLoad+Registered.transfer at split
  unfold Registered.netGain secondLoad
  linarith only [split]

theorem net_gain_positive : (1/2 : ℝ) < Registered.netGain := by
  rw [net_gain_split]
  linarith only [source_transfer_positive,(abs_le.mp first_load_error).1,(abs_le.mp second_load_error).1]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Gain
