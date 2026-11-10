import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMSourceMaxwellField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPhysicalRead
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualEMAction ActualEMCarrierOwn ActualDressedFullCoulomb ActualDressedZeroClockFrequency
open ActualDressedZeroClockVector ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold
open ActualDressedEMClockDispersion ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMNativePrincipal ActualDressedEMCorrectedCouplingSource ActualDressedEMSourceSpectrum
open ActualDressedEMVisiblePoleTransport ActualDressedEMPhysicalResidueFlux ActualDressedEMWholeUnitCovariance
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] emInsertion emOriginalJacobi correctedPhysicalClock correctedPhysicalClockJet
  emCommonSpectralRoots zeroClockClearing zeroClockFrequencyEMFraction zeroClockFrequencyDenominator
  emPhysicalLeftPoleCoefficient emCompleteLeftDefect emRightResidueDefect emFullPhysicalResidue

def sourcePhysicalPoleMode (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) : Fin 289 → ℂ :=
  actualEMZeroClockMode event eps n c.val.2 a.val

def sourcePoleTransversePotential (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) : Fin 3 → ℂ :=
  nativeTransverseRead ((eps^2 : ℝ) • n) (emInsertion.transpose*ᵥsourcePhysicalPoleMode event eps n a c)

private theorem real_source_cast (a : ℂ) (real : a.im=0) : (a.re : ℂ)=a := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · simpa only [Complex.ofReal_im] using real.symm

private theorem source_spatial_nonnegative (k : PhysicalMomentum) : 0 ≤ spatialSquare k := by
  unfold spatialSquare
  positivity

/-- This is the full actual root equation read through the action's Maxwell field strength.
No highest-EM-residue visibility is assumed, and no left-clock defect is cancelled. -/
theorem source_em_real_pole_maxwell (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (regular : (zeroClockClearing event eps n).eval a.val≠0) :
    let omega := sourceFrequency eps a.val.re
    let k := (eps^2 : ℝ) • n
    let v := sourcePhysicalPoleMode event eps n a c
    v≠0 ∧ correctedPhysicalClock event eps omega n*ᵥv=0 ∧
      sourcePhysicalMaxwellRead omega k v=
        sourceEMInducedCurrent (frequencyRay eps a.val.re n) (zeroClockQuantumResponse event eps a.val.re n) v ∧
      sourceSpatialDot k (sourcePhysicalMagnetic omega k v)=0 ∧
      sourceSpatialCross k (sourcePhysicalElectric omega k v)=(omega : ℂ) • sourcePhysicalMagnetic omega k v := by
  dsimp only
  have root := emSpectralRealRoot event eps n a c real
  have reg : (zeroClockClearing event eps n).eval (a.val.re : ℂ)≠0 := by
    rwa [real_source_cast a.val real]
  have generated := actual_source_em_physical_clock_flux event eps a.val.re n c.val.1 c.val.2
    eps_ne balanced finite reg root
  have maxwell := actual_corrected_root_principal_source event eps a.val.re n c.val.1 c.val.2
    balanced finite reg root
  have bianchi := source_em_physical_bianchi (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
    (sourcePhysicalPoleMode event eps n a c)
  simp only [real_source_cast a.val real] at generated maxwell
  refine ⟨generated.1,generated.2.1,?_,bianchi.1,bianchi.2⟩
  rw [source_em_physical_maxwell_principal]
  exact maxwell

private theorem physical_magnetic_transverse (omega : ℝ) (k : PhysicalMomentum) (v : Fin 289 → ℂ)
    (nonzero : spatialSquare k≠0) :
    sourcePhysicalMagnetic omega k v=sourceSpatialCross k (nativeTransverseRead k (emInsertion.transpose*ᵥv)) := by
  rw [source_magnetic_coordinates]
  have q : (spatialSquare k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  funext i
  fin_cases i <;> simp only [sourceSpatialCross,nativeTransverseRead]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.succ]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals field_simp [q]
  all_goals ring1

/-- Magnetic visibility is an actual source field-strength test, not a choice of a transverse input. -/
theorem source_em_magnetic_visibility (omega : ℝ) (k : PhysicalMomentum) (v : Fin 289 → ℂ)
    (nonzero : spatialSquare k≠0) (visible : sourcePhysicalMagnetic omega k v≠0) :
    nativeTransverseRead k (emInsertion.transpose*ᵥv)≠0 := by
  intro zero
  rw [physical_magnetic_transverse omega k v nonzero,zero] at visible
  apply visible
  simp [sourceSpatialCross]

/-- A nonzero coordinate is selected from the emitted transverse field; the caller supplies no chart. -/
def sourceTransverseCoordinate (v : Fin 3 → ℂ) (nonzero : v≠0) : Fin 3 := by
  classical
  have witness : ∃i,v i≠0 := by
    by_contra allzero
    push Not at allzero
    exact nonzero (funext allzero)
  exact Classical.choose witness

theorem source_transverse_coordinate_nonzero (v : Fin 3 → ℂ) (nonzero : v≠0) :
    v (sourceTransverseCoordinate v nonzero)≠0 := by
  classical
  exact Classical.choose_spec (show ∃i,v i≠0 from by
    by_contra allzero
    push Not at allzero
    exact nonzero (funext allzero))

/-- The correction is the actual full induced-current numerator divided by the source transverse
coordinate and the original action's electric/spatial coefficient. -/
def sourceTransverseSpeedCorrection (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (v : Fin 289 → ℂ) (i : Fin 3) : ℂ :=
  nativeTransverseRead ((eps^2 : ℝ) • n)
    (sourceEMInducedCurrent (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n) v) i/
      (2*(Stage9C.Material.SpinPair.lapse : ℂ)*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)*
        nativeTransverseRead ((eps^2 : ℝ) • n) (emInsertion.transpose*ᵥv) i)

structure SourceEMTransversePropagation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) where
  spatial_positive : 0<spatialSquare ((eps^2 : ℝ) • n)
  magnetic_visible : sourcePhysicalMagnetic (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
    (sourcePhysicalPoleMode event eps n a c)≠0
  transverse_visible : sourcePoleTransversePotential event eps n a c≠0
  coordinate : Fin 3
  coordinate_nonzero : sourcePoleTransversePotential event eps n a c coordinate≠0
  full_kernel : correctedPhysicalClock event eps (sourceFrequency eps a.val.re) n*ᵥ
    sourcePhysicalPoleMode event eps n a c=0
  faraday : sourceSpatialCross ((eps^2 : ℝ) • n)
    (sourcePhysicalElectric (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
      (sourcePhysicalPoleMode event eps n a c))=
    (sourceFrequency eps a.val.re : ℂ) •
      sourcePhysicalMagnetic (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
        (sourcePhysicalPoleMode event eps n a c)
  corrected_speed_source : (actualRootPhaseSpeedSquared eps a.val.re n : ℂ)=
    (nativePrimitiveSpeed : ℂ)^2+sourceTransverseSpeedCorrection event eps a.val.re n
      (sourcePhysicalPoleMode event eps n a c) coordinate
  complete_energy : EMSourceRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne
    (emSpectralRealRoot event eps n a c real)

def sourceEMTransversePropagation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (regular : (zeroClockClearing event eps n).eval a.val≠0)
    (q_ne : spatialSquare ((eps^2 : ℝ) • n)≠0)
    (magnetic : sourcePhysicalMagnetic (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
      (sourcePhysicalPoleMode event eps n a c)≠0) :
    SourceEMTransversePropagation event eps n eps_ne a c real := by
  have transverse := source_em_magnetic_visibility (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
    (sourcePhysicalPoleMode event eps n a c) q_ne magnetic
  let i := sourceTransverseCoordinate (sourcePoleTransversePotential event eps n a c) transverse
  have i_ne : sourcePoleTransversePotential event eps n a c i≠0 :=
    source_transverse_coordinate_nonzero (sourcePoleTransversePotential event eps n a c) transverse
  have source := source_em_real_pole_maxwell event eps n eps_ne balanced finite a c real regular
  have reg : (zeroClockClearing event eps n).eval (a.val.re : ℂ)≠0 := by
    rwa [real_source_cast a.val real]
  have speed := actual_corrected_root_speed_component_price event eps a.val.re n c.val.1 c.val.2
    balanced finite reg (emSpectralRealRoot event eps n a c real) q_ne i
    (by simpa only [sourcePoleTransversePotential,sourcePhysicalPoleMode,real_source_cast a.val real] using i_ne)
  exact {
    spatial_positive := lt_of_le_of_ne (source_spatial_nonnegative _) (Ne.symm q_ne)
    magnetic_visible := magnetic
    transverse_visible := transverse
    coordinate := i
    coordinate_nonzero := i_ne
    full_kernel := source.2.1
    faraday := source.2.2.2.2
    corrected_speed_source := by simpa only [sourceTransverseSpeedCorrection,sourceEMInducedCurrent,
      sourcePhysicalPoleMode,real_source_cast a.val real] using speed
    complete_energy := sourceEMRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne balanced finite reg
      (emSpectralRealRoot event eps n a c real)
  }

inductive EMPhysicalPropagationReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) : Type
  | nonreal (imaginary : a.val.im≠0) (observation : EMActualSpectralObservation event eps n eps_ne a c)
  | clearing (real : a.val.im=0) (zero : (zeroClockClearing event eps n).eval a.val=0)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)
  | zeroMomentum (real : a.val.im=0) (zero : spatialSquare ((eps^2 : ℝ) • n)=0)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)
      (energy : EMSourceRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne (emSpectralRealRoot event eps n a c real))
  | longitudinal (real : a.val.im=0)
      (zero : sourcePhysicalMagnetic (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
        (sourcePhysicalPoleMode event eps n a c)=0)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)
      (energy : EMSourceRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne (emSpectralRealRoot event eps n a c real))
  | transverse (real : a.val.im=0)
      (propagation : SourceEMTransversePropagation event eps n eps_ne a c real)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)

/-- Each original root and observer is classified by its actual source field strength.
The complete original principal/analytic and sigma/frequency energy debts remain in every branch. -/
def sourceEMPhysicalPropagationReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (tensor : EMTensorClockFinite event eps n)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) :
    EMPhysicalPropagationReturn event eps n eps_ne a c := by
  classical
  cases sourceEMSpectralBranchReturn event eps n eps_ne tensor balanced finite a c with
  | nonreal imaginary observation => exact .nonreal imaginary observation
  | clearingFailure real zero observation => exact .clearing real zero observation
  | physical real regular observation energy =>
    by_cases q : spatialSquare ((eps^2 : ℝ) • n)=0
    · exact .zeroMomentum real q observation energy
    · by_cases magnetic : sourcePhysicalMagnetic (sourceFrequency eps a.val.re) ((eps^2 : ℝ) • n)
        (sourcePhysicalPoleMode event eps n a c)=0
      · exact .longitudinal real magnetic observation energy
      · exact .transverse real (sourceEMTransversePropagation event eps n eps_ne balanced finite a c real regular q magnetic) observation

end LowEnergy.GaussComposite.ActualDressedEMPhysicalRead
