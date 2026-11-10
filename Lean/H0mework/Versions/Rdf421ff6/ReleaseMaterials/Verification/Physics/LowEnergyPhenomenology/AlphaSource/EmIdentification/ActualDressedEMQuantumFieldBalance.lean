import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockQuantumResidue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMQuantumThreshold
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedUniformMaterialCoefficients
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualDressedZeroClockVector ActualDressedEMZeroClockColumns ActualDressedFrequencyHalf
open ActualEMAction ActualEMDressedSchur ActualEMDressedConstraint ActualEMCurrentSplit ActualEMCarrierOwn
open ActualDressedNativeConstraint PreparationVacuumPhysicalModeContact
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedVisiblePole
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] frequencyHalfPolarization sourceCokernel emInsertion emOriginalJacobi

/-- The four actual EM rows retain their full residual forcing, as well as the original quantum matrix. -/
theorem actual_zero_clock_em_full_mixed_balance (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    let J := emOriginalJacobi (frequencyRay eps s n)
    let Q := zeroClockQuantumResponse event eps s n
    (emInsertion.transpose*J*emInsertion-emInsertion.transpose*Q*emInsertion)*ᵥemCoordinateCurrent v=
      emInsertion.transpose*ᵥ((Q-J)*ᵥemCurrentResidual v) := by
  dsimp only
  let v := actualEMZeroClockMode event eps n nu (s : ℂ)
  have balance := actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root
  dsimp only at balance
  have whole := (source_mode_full_decomposition v).1
  have observed := congrArg (fun w : Fin 289 → ℂ => emInsertion.transpose*ᵥw) balance
  change emInsertion.transpose*ᵥ(emOriginalJacobi (frequencyRay eps s n)*ᵥv)=
    emInsertion.transpose*ᵥ(zeroClockQuantumResponse event eps s n*ᵥv) at observed
  rw [whole] at observed
  simp only [Matrix.mulVec_add] at observed
  simp only [Matrix.mulVec_mulVec] at observed
  simp only [Matrix.sub_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_sub]
  simp only [Matrix.mul_assoc] at observed ⊢
  exact (sub_eq_sub_iff_add_eq_add).mpr (observed.trans (add_comm _ _))

/-- All nine original compatibility rows consume the same full quantum feedback mode. -/
theorem actual_zero_clock_em_quantum_constraint (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    sourceCokernel (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n*ᵥv)=0 := by
  dsimp only
  let v := actualEMZeroClockMode event eps n nu (s : ℂ)
  have balance := actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root
  dsimp only at balance
  rw [← balance,em_jacobi_source]
  exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)

/-- The original quantum Ward matrix is sigma-normalized once and returns to the generated nine-row zero. -/
theorem actual_zero_clock_em_quantum_nine_null (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    Tendsto (fun sigma : ℝ => (sigma : ℂ) • sourceCokernel (frequencyRay eps s n)
      (frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)*ᵥv))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  dsimp only
  let v := actualEMZeroClockMode event eps n nu (s : ℂ)
  have continuous : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
      sourceCokernel (frequencyRay eps s n) (M*ᵥv)) := by
    exact (sourceCokernel (frequencyRay eps s n)).toContinuousLinearMap.continuous.comp
      (by unfold Matrix.mulVec dotProduct; fun_prop)
  have limit := (continuous.tendsto _).comp
    (actual_zero_clock_full_quantum_matrix event eps s n regular balanced)
  rw [actual_zero_clock_em_quantum_constraint event eps s n mu nu balanced finite regular root] at limit
  simpa only [Function.comp_def,Matrix.smul_mulVec,map_smul] using limit

end LowEnergy.GaussComposite.ActualDressedEMQuantumThreshold
