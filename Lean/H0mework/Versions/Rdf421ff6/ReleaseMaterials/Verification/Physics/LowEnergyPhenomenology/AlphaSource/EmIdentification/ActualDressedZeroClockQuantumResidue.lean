import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMColumnModes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMQuantumThreshold
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedUniformMaterialCoefficients ActualDressedEMTensorClock
open ActualDressedOrderedStatic ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedFrequencyHalf ActualEMAction ActualEMDressedSchur
open PreparationVacuumPhysicalModeContact Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] commonClearedPencil commonDenominator commonNumerator commonJacobi
  emOriginalJacobi frequencyResponsePencil frequencyHalfPolarization

/-- The full original quantum numerator is retained before taking its source clock residue. -/
def fullClockQuantumNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) (ℂ[X])[X] := (commonNumerator event n).map (frequencyClockSlice eps)

def zeroClockQuantumNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ[X] :=
  fun i j => (X*fullClockQuantumNumerator event eps n i j).coeff (clearingClockOrder event eps n)

def zeroClockQuantumResponse (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => (zeroClockQuantumNumerator event eps n i j).eval (s : ℂ)/
    (zeroClockClearing event eps n).eval (s : ℂ)

private theorem source_polynomial_constant (P : ℂ[X]) (c : ℂ)
    (same : ∀r : ℝ, P.eval (r : ℂ)=c) : P=Polynomial.C c := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨r,rfl⟩
  change P.eval (r : ℂ)=(Polynomial.C c).eval (r : ℂ)
  simpa only [Polynomial.eval_C] using same r

private theorem actual_clock_jacobi_constant (eps s : ℝ) (n : PhysicalMomentum) (i j : Fin 289) :
    frequencyDampingSlice eps s (commonJacobi n i j)=
      Polynomial.C (emOriginalJacobi (frequencyRay eps s n) i j) := by
  apply source_polynomial_constant
  intro sigma
  rw [frequency_damping_eval]
  exact congrFun (congrFun (common_jacobi_eval n eps sigma s) i) j

/-- Same source H=dJ-sigma*N; its original J is clock-constant, not a new approximation. -/
theorem actual_clock_quantum_polynomial (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (i j : Fin 289) :
    clockSpecialize s (fullClockPencil event eps n i j)=
      clockSpecialize s (fullClockClearing event eps n)*
        Polynomial.C (emOriginalJacobi (frequencyRay eps s n) i j)-
      X*clockSpecialize s (fullClockQuantumNumerator event eps n i j) := by
  unfold fullClockPencil fullClockClearing fullClockQuantumNumerator
  simp only [Matrix.map_apply,frequency_clock_specialize]
  unfold commonClearedPencil
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,map_sub,map_mul]
  rw [actual_clock_jacobi_constant]
  have sigma : frequencyDampingSlice eps s (MvPolynomial.X 1)=Polynomial.X := by
    simp [frequencyDampingSlice]
  rw [sigma]

/-- The surviving original quantum term is N_(b-1), with b fixed by the original clearing polynomial. -/
theorem source_quantum_clock_coefficient (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (i j : Fin 289) :
    zeroClockQuantumNumerator event eps n i j=
      if clearingClockOrder event eps n=0 then 0
      else (fullClockQuantumNumerator event eps n i j).coeff (clearingClockOrder event eps n-1) := by
  unfold zeroClockQuantumNumerator
  cases order : clearingClockOrder event eps n with
  | zero => simp
  | succ k => simp only [Nat.succ_ne_zero,if_false,Nat.add_one_sub_one,coeff_X_mul]

/-- The same actual threshold retains the full quantum residue instead of assuming its vanishing. -/
theorem actual_zero_clock_cleared_quantum (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) :
    (zeroClockPencil event eps n).map (Polynomial.eval (s : ℂ))=
      (zeroClockClearing event eps n).eval (s : ℂ) • emOriginalJacobi (frequencyRay eps s n)-
        (zeroClockQuantumNumerator event eps n).map (Polynomial.eval (s : ℂ)) := by
  ext i j
  have coefficient := congrArg (fun P : ℂ[X] => P.coeff (clearingClockOrder event eps n))
    (actual_clock_quantum_polynomial event eps s n i j)
  have specialize (P : (ℂ[X])[X]) (k : ℕ) :
      (clockSpecialize s P).coeff k=(P.coeff k).eval (s : ℂ) := by
    simp only [clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
    rfl
  have feedback : X*clockSpecialize s (fullClockQuantumNumerator event eps n i j)=
      clockSpecialize s (X*fullClockQuantumNumerator event eps n i j) := by
    rw [map_mul]
    simp [clockSpecialize]
  rw [Polynomial.coeff_sub,Polynomial.coeff_mul_C,feedback] at coefficient
  simp only [specialize] at coefficient
  simpa only [zeroClockPencil,zeroClockClearing,zeroClockQuantumNumerator,Matrix.map_apply,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] using coefficient

theorem actual_zero_clock_threshold_quantum (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0) :
    zeroClockThresholdPencil event eps s n=
      emOriginalJacobi (frequencyRay eps s n)-zeroClockQuantumResponse event eps s n := by
  ext i j
  have cleared := congrFun (congrFun (actual_zero_clock_cleared_quantum event eps s n) i) j
  change (zeroClockPencil event eps n i j).eval (s : ℂ)=
    (zeroClockClearing event eps n).eval (s : ℂ)*emOriginalJacobi (frequencyRay eps s n) i j-
      (zeroClockQuantumNumerator event eps n i j).eval (s : ℂ) at cleared
  unfold zeroClockThresholdPencil zeroClockQuantumResponse
  change (zeroClockPencil event eps n i j).eval (s : ℂ)/(zeroClockClearing event eps n).eval (s : ℂ)=
    emOriginalJacobi (frequencyRay eps s n) i j-
      (zeroClockQuantumNumerator event eps n i j).eval (s : ℂ)/(zeroClockClearing event eps n).eval (s : ℂ)
  rw [cleared]
  field_simp [regular]

/-- This is the actual sigma-normalized full quantum matrix limit, before selecting any mode or EM read. -/
theorem actual_zero_clock_full_quantum_matrix (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (balanced : PencilClockBalanced event eps n) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ) •
      frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockQuantumResponse event eps s n)) := by
  have pencil := actual_zero_clock_threshold_pencil event eps s n regular balanced
  have constant : Tendsto (fun _ : ℝ => emOriginalJacobi (frequencyRay eps s n))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay eps s n))) := tendsto_const_nhds
  have limit := constant.sub pencil
  rw [actual_zero_clock_threshold_quantum event eps s n regular] at limit
  simp only [sub_sub_cancel] at limit
  apply Tendsto.congr' _ limit
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  rw [damped_source_sheet_response event eps s sigma n positive]
  abel

/-- Every original real EM root pays Jv=Q0v on the original independent clearing chart. -/
theorem actual_zero_clock_em_original_balance (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈LowEnergy.ActualDressedVisiblePole.visibleRoots
      (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    emOriginalJacobi (frequencyRay eps s n)*ᵥv=zeroClockQuantumResponse event eps s n*ᵥv := by
  have kernel := actual_zero_clock_em_threshold_kernel event eps s n mu nu balanced finite regular root
  rw [actual_zero_clock_threshold_quantum event eps s n regular,Matrix.sub_mulVec] at kernel
  exact sub_eq_zero.mp kernel

end LowEnergy.GaussComposite.ActualDressedEMQuantumThreshold
