import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Consumers
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Bounds
open Collision Quantum Resource Propagation.Interface Propagation.Producer Load.Source Load.Producer.StrictThermal
open Blocks Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem diagonal_energy_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (trace : rho.trace=1)
    (low : ℝ) (bound : ∀ i, low ≤ d i) :
    low ≤ energy (Matrix.diagonal (fun i => (d i : ℂ))) rho := by
  have mass : ∑ i, (rho i i).re=1 := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum,Complex.one_re] using congrArg Complex.re trace
  have read : energy (Matrix.diagonal (fun i => (d i : ℂ))) rho=∑ i, d i*(rho i i).re := by
    simp [energy,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Complex.mul_re]
  rw [read]
  calc
    low = ∑ i, low*(rho i i).re := by rw [← Finset.mul_sum,mass,mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (bound i) (Complex.nonneg_iff.mp (positive.diag_nonneg (i := i))).1

theorem calculated_lower (i : Basis) : -(1868/100 : ℝ) ≤ Donor.calculatedEnergy i := by
  have low := Inverse.Scaled.Order.source_energy_increasing.monotone (Fin.zero_le i)
  rw [Inverse.Scaled.Finite.energy_0_exact] at low
  linarith only [low]

theorem source_energy_lower (i : Basis) : -(1869/100 : ℝ) < Preparation.sourceEnergies i := by
  let rho := Spectrum.spectralPure A (Propagation.Dynamics.activeMatrix_hermitian Propagation.Source.electronicSource) i
  have positive : rho.PosSemidef := Spectrum.spectralPure_positive _ _ _
  have trace : rho.trace=1 := Spectrum.spectralPure_trace _ _ _
  have actual : energy A rho=Preparation.sourceEnergies i := Spectrum.spectralPure_energy _ _ _
  have error := actual_energy_error rho positive
  rw [trace,Complex.one_re,mul_one,actual] at error
  have coordsPositive : (sourceCoordinates rho).PosSemidef := conjugation_posSemidef _ _ positive
  have coordsTrace : (sourceCoordinates rho).trace=1 := (conjugation_trace _ _).trans trace
  have bound := diagonal_energy_lower Donor.calculatedEnergy (sourceCoordinates rho)
    coordsPositive coordsTrace (-(1868/100 : ℝ)) calculated_lower
  have same : E=Matrix.diagonal (fun j => (Donor.calculatedEnergy j : ℂ)) := by
    ext j k
    simp [E,Donor.calculatedEnergy,Matrix.diagonal,Complex.ofReal_div]
  rw [← same] at bound
  have lower := (abs_le.mp error).1
  linarith only [bound,lower]

private theorem eigenvalue_has_block {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (label : ι → κ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (kept : Preserves label H)
    (a : ι) :
    ∃ k, (restrict label k H-(hH.eigenvalues a : ℂ) • 1).det=0 := by
  classical
  by_contra absent
  have invertible : ∀ k, (restrict label k H-(hH.eigenvalues a : ℂ) • 1).det ≠ 0 := by
    simpa only [not_exists] using absent
  have vectorZero (i : ι) : (hH.eigenvectorUnitary : Matrix ι ι ℂ) i a=0 := by
    have localZero := eigenvector_block_zero kept
      (fun j => (hH.eigenvectorUnitary : Matrix ι ι ℂ) j a)
      (hH.eigenvalues a : ℂ) (by
        have eigen := hH.mulVec_eigenvectorBasis a
        funext j
        simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply,Pi.smul_apply,Complex.real_smul,smul_eq_mul] using
          congrFun eigen j) (label i) (invertible (label i))
    exact congrArg (fun v => v ⟨i,rfl⟩) localZero
  have zero : Spectrum.spectralPure H hH a=0 := by
    ext i j
    rw [spectralPure_entry,vectorZero,zero_mul]
    rfl
  have normalized := Spectrum.spectralPure_trace H hH a
  rw [zero,Matrix.trace_zero] at normalized
  exact zero_ne_one normalized

theorem powered_energy_lower (i : PairController) :
    -(3838/100 : ℝ) < Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i := by
  by_contra bad
  have low : Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i ≤ -(3838/100 : ℝ) := le_of_not_gt bad
  obtain ⟨k,singular⟩ := eigenvalue_has_block pcOrbit Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian source_hpc_preserves i
  have every (k : Sym2 Basis) :
      (restrict pcOrbit k Powered.Producer.poweredTotalHamiltonian-
        (Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i : ℂ) • 1).det ≠ 0 := by
    refine Sym2.inductionOn k ?_
    intro a b
    have ha := source_energy_lower a
    have hb := source_energy_lower b
    by_cases same : a=b
    · subst b
      rw [original_diagonal_resolvent]
      apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (show 0 < 2*Preparation.sourceEnergies a+1-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [ha,low]))
      · exact_mod_cast (ne_of_gt (show 0 < 2*Preparation.sourceEnergies a+3-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [ha,low]))
    · rw [original_offDiagonal_resolvent a b same]
      repeat' apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (show 0 < Preparation.sourceEnergies a+Preparation.sourceEnergies b-1-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [ha,hb,low]))
      · exact_mod_cast (ne_of_gt (show 0 < Preparation.sourceEnergies a+Preparation.sourceEnergies b+3-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [ha,hb,low]))
      · exact_mod_cast (ne_of_gt (show 0 < 2*Preparation.sourceEnergies a+1-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [ha,low]))
      · exact_mod_cast (ne_of_gt (show 0 < 2*Preparation.sourceEnergies b+1-
          Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues i by linarith only [hb,low]))
  exact every k singular

private def twoPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) : Matrix ι ι ℂ :=
  let v : ι → ℂ := Pi.single a 1-Pi.single b 1
  (1/2 : ℝ) • Matrix.vecMulVec v (star v)

private theorem twoPoint_positive {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    (twoPoint a b).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1/2)

private theorem twoPoint_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (different : a ≠ b) :
    (twoPoint a b).trace=1 := by
  simp [twoPoint,Matrix.trace_smul,Matrix.trace_vecMulVec,dotProduct,Pi.single_apply,
    mul_sub,Finset.sum_sub_distrib,different,Ne.symm different]
  norm_num

private theorem twoPoint_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (a b : ι) :
    energy H (twoPoint a b)=((H a a).re+(H b b).re-(H a b).re-(H b a).re)/2 := by
  simp [twoPoint,energy,Matrix.trace_smul,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,
    Matrix.mulVec, dotProduct,Pi.single_apply,mul_sub,Finset.sum_sub_distrib,
    Complex.mul_re,Complex.sub_re]
  ring

def trial : Matrix PairController PairController ℂ :=
  twoPoint (((0 : Basis),(1 : Basis)),(0 : Fin 2)) (((1 : Basis),(0 : Basis)),(0 : Fin 2))

theorem trial_positive : trial.PosSemidef := twoPoint_positive _ _
theorem trial_trace : trial.trace=1 := twoPoint_trace _ _ (by decide)

theorem calculated_trial_energy : energy (sourcePCH E) trial=
    Donor.calculatedEnergy 0+Donor.calculatedEnergy 1-1 := by
  rw [trial,twoPoint_energy]
  have read := hpc_scalar_block Donor.calculatedEnergy (0 : Basis) (1 : Basis) (by decide)
  have scalarE : E=Matrix.diagonal (fun i => (Donor.calculatedEnergy i : ℂ)) := by
    ext i j
    simp [E,Donor.calculatedEnergy,Matrix.diagonal,Complex.ofReal_div]
  have block : (sourcePCH E).submatrix (orbitPC (0 : Basis) (1 : Basis)) (orbitPC (0 : Basis) (1 : Basis))=
      scalarHpc (Donor.calculatedEnergy 0) (Donor.calculatedEnergy 1) := by
    rw [scalarE]
    exact read
  have aa := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0,0) (0,0)) block
  have bb := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (1,0) (1,0)) block
  have ab := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0,0) (1,0)) block
  have ba := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (1,0) (0,0)) block
  change sourcePCH E ((0,1),0) ((0,1),0)=((Donor.calculatedEnergy 0+Donor.calculatedEnergy 1 : ℝ) : ℂ) at aa
  change sourcePCH E ((1,0),0) ((1,0),0)=((Donor.calculatedEnergy 0+Donor.calculatedEnergy 1 : ℝ) : ℂ) at bb
  change sourcePCH E ((0,1),0) ((1,0),0)=1 at ab
  change sourcePCH E ((1,0),0) ((0,1),0)=1 at ba
  rw [aa,bb,ab,ba]
  simp
  ring

private theorem energy_pulled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    energy O (Quantum.conjugation U rho)=energy (Quantum.conjugation (star U) O) rho :=
  Load.Producer.StrictThermal.energy_pullback O rho U

theorem powered_ground_upper :
    Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues Spectrum.lastIndex < -(383/10 : ℝ) := by
  let U := Powered.Source.controllerFrame originalToCalculated
  let actualTrial := conjugation (star U) trial
  have positive : actualTrial.PosSemidef := conjugation_posSemidef _ _ trial_positive
  have trace : actualTrial.trace=1 := (conjugation_trace _ _).trans trial_trace
  have floor := (Spectrum.energy_spectral_bounds Powered.Producer.poweredTotalHamiltonian actualTrial
    Powered.Producer.poweredTotalHamiltonian_hermitian positive trace).1
  have read : energy Powered.Producer.poweredTotalHamiltonian actualTrial=
      energy (conjugation U Powered.Producer.poweredTotalHamiltonian) trial := by
    have h := energy_pulled Powered.Producer.poweredTotalHamiltonian trial (star U)
    rw [star_star] at h
    exact h
  have error := energy_norm_mass
    (conjugation U Powered.Producer.poweredTotalHamiltonian-sourcePCH E) trial trial_positive
  rw [trial_trace,Complex.one_re,mul_one] at error
  have bound := error.trans actual_powered_Hamiltonian_error
  rw [Load.Producer.HeatProbability.energy_sub_left,← read,calculated_trial_energy,
    Inverse.Scaled.Finite.energy_0_exact,Inverse.Scaled.Finite.energy_1_exact] at bound
  have hi := (abs_le.mp bound).2
  linarith only [floor,hi]

private theorem lower_shift_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (low : ℝ)
    (bound : ∀ i, low ≤ hH.eigenvalues i) : (H-(low : ℂ) • 1).PosSemidef := by
  let D := Matrix.diagonal (fun i => ((hH.eigenvalues i-low : ℝ) : ℂ))
  have positiveD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    exact_mod_cast (sub_nonneg.mpr (bound i)))
  have coordinates : Quantum.conjugation (star hH.eigenvectorUnitary) (H-(low : ℂ) • 1)=D := by
    change Unitary.conjStarAlgAut ℂ _ (star hH.eigenvectorUnitary) (H-(low : ℂ) • 1)=D
    rw [map_sub,hH.conjStarAlgAut_star_eigenvectorUnitary,map_smul,map_one]
    ext i j
    by_cases same : i=j
    · subst j; simp [D,Matrix.diagonal,Complex.ofReal_sub]
    · simp [D,Matrix.diagonal,same]
  have positive := conjugation_posSemidef hH.eigenvectorUnitary D positiveD
  rw [← coordinates] at positive
  change (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
    (Unitary.conjStarAlgAut ℂ _ (star hH.eigenvectorUnitary) (H-(low : ℂ) • 1))).PosSemidef at positive
  rw [← Unitary.conjStarAlgAut_mul_apply] at positive
  simpa using positive

theorem powered_shift_positive :
    (Powered.Producer.poweredTotalHamiltonian+(192/5 : ℝ) • 1).PosSemidef := by
  have lower := lower_shift_positive Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (-(384/10 : ℝ))
    (fun i => by have paid := powered_energy_lower i; linarith only [paid])
  convert lower using 1
  ext i j
  norm_num [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]

theorem powered_top_upper :
    Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues Spectrum.firstIndex < (93/10 : ℝ) := by
  have actual := Spectral.Projection.actual_donor_eigenvalue
  have top := Spectral.Producer.source_top_upper
  change Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues Spectrum.firstIndex=_ at actual
  linarith only [actual,top]

theorem powered_buffer_positive :
    (Powered.Producer.poweredTotalHamiltonian+(1919/50 : ℝ) • 1).PosSemidef := by
  have lower := lower_shift_positive Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (-(3838/100 : ℝ))
    (fun i => (powered_energy_lower i).le)
  convert lower using 1
  ext i j
  norm_num [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]

private theorem conjugation_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) (r : ℝ) :
    conjugation U (H+r • 1)=conjugation U H+r • 1 := by
  change Unitary.conjStarAlgAut ℂ _ U (H+(r : ℂ) • 1)=Unitary.conjStarAlgAut ℂ _ U H+(r : ℂ) • 1
  rw [map_add,map_smul,map_one]

theorem calculated_shift_positive : (sourcePCH E+(192/5 : ℝ) • 1).PosSemidef := by
  let U := Powered.Source.controllerFrame originalToCalculated
  let C := conjugation U Powered.Producer.poweredTotalHamiltonian
  have source := conjugation_posSemidef U _ powered_buffer_positive
  rw [conjugation_shift] at source
  change (C+(1919/50 : ℝ) • 1).PosSemidef at source
  have hermitian : (C-sourcePCH E).IsHermitian :=
    (Inverse.Scaled.Finite.Prepared.conjugation_hermitian _ _ Powered.Producer.poweredTotalHamiltonian_hermitian).sub numeric_PC_hermitian
  have up : C-sourcePCH E ≤ (1/50 : ℝ) • 1 := by
    have read := hermitian.isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at read
    exact read.trans (smul_le_smul_of_nonneg_right
      (actual_powered_Hamiltonian_error.trans (by norm_num)) zero_le_one)
  have remainder : ((1/50 : ℝ) • 1-(C-sourcePCH E)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr up)
  have sum := source.add remainder
  convert sum using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]
  push_cast
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Bounds
