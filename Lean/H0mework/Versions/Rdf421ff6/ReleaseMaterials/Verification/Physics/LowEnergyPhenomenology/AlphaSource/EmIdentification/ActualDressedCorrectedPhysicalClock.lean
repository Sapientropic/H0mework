import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativePhysicalClock
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMClockDispersion
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualEMAction ActualEMDressedSchur ActualEMCarrierOwn
open ActualDressedZeroClockVector ActualDressedZeroClockFrequency ActualDressedEMZeroClockColumns
open ActualDressedEMQuantumThreshold ActualDressedFrequencyHalf
open LowEnergy.ActualDressedVisiblePole
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] emOriginalJacobi emInsertion frequencyResponsePencil frequencyHalfPolarization

def physicalQuantumResponse (event : DressedEvent) (eps omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ := zeroClockQuantumResponse event eps (omega/eps^2) n

/-- Full quotient derivative of the same original N_(b-1)/d_b, with the physical epsilon-squared chain paid. -/
def physicalQuantumClockJet (event : DressedEvent) (eps omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ := fun i j =>
  let N := zeroClockQuantumNumerator event eps n i j
  let d := zeroClockClearing event eps n
  let s : ℂ := ((omega/eps^2 : ℝ) : ℂ)
  (N.derivative.eval s*d.eval s-N.eval s*d.derivative.eval s)/((eps^2 : ℂ)*(d.eval s)^2)

def correctedPhysicalClock (event : DressedEvent) (eps omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  emOriginalJacobi (physicalFrequencyMomentum omega ((eps^2 : ℝ) • n))-physicalQuantumResponse event eps omega n

def correctedPhysicalClockJet (event : DressedEvent) (eps omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  nativePhysicalClockJet omega ((eps^2 : ℝ) • n)-physicalQuantumClockJet event eps omega n

private theorem physical_polynomial_quotient_derivative (N d : ℂ[X]) (eps omega : ℝ)
    (_nonzero : eps≠0) (regular : d.eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun w : ℝ => N.eval ((w/eps^2 : ℝ) : ℂ)/d.eval ((w/eps^2 : ℝ) : ℂ))
      ((N.derivative.eval ((omega/eps^2 : ℝ) : ℂ)*d.eval ((omega/eps^2 : ℝ) : ℂ)-
          N.eval ((omega/eps^2 : ℝ) : ℂ)*d.derivative.eval ((omega/eps^2 : ℝ) : ℂ))/
        ((eps^2 : ℂ)*(d.eval ((omega/eps^2 : ℝ) : ℂ))^2)) omega := by
  have ratio := ((N.hasDerivAt ((omega/eps^2 : ℝ) : ℂ)).div
    (d.hasDerivAt ((omega/eps^2 : ℝ) : ℂ)) regular).comp_ofReal
  have scale : HasDerivAt (fun w : ℝ => w/eps^2) (1/eps^2) omega :=
    (hasDerivAt_id omega).div_const (eps^2)
  have chain := ratio.scomp omega scale
  have coefficient : (1/eps^2 : ℝ) •
      ((N.derivative.eval ((omega/eps^2 : ℝ) : ℂ)*d.eval ((omega/eps^2 : ℝ) : ℂ)-
        N.eval ((omega/eps^2 : ℝ) : ℂ)*d.derivative.eval ((omega/eps^2 : ℝ) : ℂ))/
        (d.eval ((omega/eps^2 : ℝ) : ℂ))^2)=
      (N.derivative.eval ((omega/eps^2 : ℝ) : ℂ)*d.eval ((omega/eps^2 : ℝ) : ℂ)-
        N.eval ((omega/eps^2 : ℝ) : ℂ)*d.derivative.eval ((omega/eps^2 : ℝ) : ℂ))/
        ((eps^2 : ℂ)*(d.eval ((omega/eps^2 : ℝ) : ℂ))^2) := by
    rw [Complex.real_smul]
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow]
    have chart : d.eval ((omega : ℂ)/(eps : ℂ)^2)≠0 := by
      simpa only [Complex.ofReal_div,Complex.ofReal_pow] using regular
    field_simp [chart,pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr _nonzero)]
  rw [coefficient] at chain
  simpa only [Function.comp_def,Pi.div_apply] using chain

theorem actual_physical_quantum_clock_derivative (event : DressedEvent) (eps omega : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun w : ℝ => physicalQuantumResponse event eps w n)
      (physicalQuantumClockJet event eps omega n) omega := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  exact physical_polynomial_quotient_derivative _ _ eps omega nonzero regular

set_option backward.isDefEq.respectTransparency false in
theorem actual_corrected_physical_clock_derivative (event : DressedEvent) (eps omega : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun w : ℝ => correctedPhysicalClock event eps w n)
      (correctedPhysicalClockJet event eps omega n) omega := by
  have native := actual_native_physical_clock_derivative omega ((eps^2 : ℝ) • n)
  have quantum := actual_physical_quantum_clock_derivative event eps omega n nonzero regular
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have nativeEntry := (hasDerivAt_pi.mp (hasDerivAt_pi.mp native i)) j
  have quantumEntry := (hasDerivAt_pi.mp (hasDerivAt_pi.mp quantum i)) j
  simpa only [correctedPhysicalClock,correctedPhysicalClockJet,Matrix.sub_apply] using nativeEntry.fun_sub quantumEntry

theorem source_physical_clock_point (eps omega : ℝ) (nonzero : eps≠0) :
    sourceFrequency eps (omega/eps^2)=omega := by
  unfold sourceFrequency
  field_simp [pow_ne_zero 2 nonzero]

/-- This is the existing actual P0 at the original physical frequency and length coordinates. -/
theorem actual_corrected_physical_threshold (event : DressedEvent) (eps omega : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    correctedPhysicalClock event eps omega n=zeroClockThresholdPencil event eps (omega/eps^2) n := by
  unfold correctedPhysicalClock physicalQuantumResponse
  rw [actual_zero_clock_threshold_quantum event eps (omega/eps^2) n regular]
  rw [← actual_physical_frequency_ray eps (omega/eps^2) n,source_physical_clock_point eps omega nonzero]

/-- Physical sigma-first response is returned before taking the source-generated clock derivative. -/
theorem actual_corrected_physical_clock_limit (event : DressedEvent) (eps omega : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0)
    (balanced : PencilClockBalanced event eps n) :
    Tendsto (fun sigma : ℝ => frequencyResponsePencil event ((eps^2 : ℝ) • n)
      (physicalFrequencyMomentum omega ((eps^2 : ℝ) • n)) (dampedFourierClock omega sigma))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (correctedPhysicalClock event eps omega n)) := by
  have limit := actual_zero_clock_threshold_pencil event eps (omega/eps^2) n regular balanced
  rw [← actual_corrected_physical_threshold event eps omega n nonzero regular] at limit
  rw [← actual_physical_frequency_ray eps (omega/eps^2) n,source_physical_clock_point eps omega nonzero] at limit
  exact limit

private theorem observed_matrix_derivative (M M' : ℝ → Matrix (Fin 289) (Fin 289) ℂ)
    (omega : ℝ) (fd v : Fin 289 → ℂ) (paid : HasDerivAt M (M' omega) omega) :
    HasDerivAt (fun w : ℝ => dotProduct fd (M w*ᵥv))
      (dotProduct fd (M' omega*ᵥv)) omega := by
  simp only [Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp paid i)) j).mul_const (v j)

/-- The held full source mode enters the actual corrected clock flux without a caller normalization. -/
theorem actual_source_em_physical_clock_flux (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (nonzero : eps≠0)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let v := actualEMZeroClockMode event eps n nu (s : ℂ)
    let omega := sourceFrequency eps s
    v≠0 ∧ correctedPhysicalClock event eps omega n*ᵥv=0 ∧
      HasDerivAt (fun w : ℝ => dotProduct (fun i => emInsertion i mu)
        (correctedPhysicalClock event eps w n*ᵥv))
        (dotProduct (fun i => emInsertion i mu) (correctedPhysicalClockJet event eps omega n*ᵥv)) omega := by
  dsimp only
  have point : sourceFrequency eps s/eps^2=s := by
    unfold sourceFrequency
    exact mul_div_cancel_left₀ s (pow_ne_zero 2 nonzero)
  have physicalRegular : (zeroClockClearing event eps n).eval
      ((sourceFrequency eps s/eps^2 : ℝ) : ℂ)≠0 := by rw [point];exact regular
  refine ⟨(actual_zero_clock_em_full_mode event eps n mu nu (s : ℂ) balanced finite root).1,?_,?_⟩
  · rw [actual_corrected_physical_threshold event eps (sourceFrequency eps s) n nonzero physicalRegular,point]
    exact actual_zero_clock_em_threshold_kernel event eps s n mu nu balanced finite regular root
  · exact observed_matrix_derivative (correctedPhysicalClock event eps · n)
      (correctedPhysicalClockJet event eps · n) (sourceFrequency eps s)
      (fun i => emInsertion i mu) (actualEMZeroClockMode event eps n nu (s : ℂ))
      (actual_corrected_physical_clock_derivative event eps (sourceFrequency eps s) n nonzero physicalRegular)

end LowEnergy.GaussComposite.ActualDressedEMClockDispersion
