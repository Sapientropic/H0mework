import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMGeneratedSpectralBranches

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMTensorClock ActualDressedEMPolePairEnergy
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux ActualDressedEMPhysicalResidueFlux
open ActualDressedEMVisiblePoleTransport ActualDressedEMQuantumThreshold ActualDressedEMSourceTransport
open ActualDressedEMClockDispersion
open ActualDressedCorrectedGreen ActualDressedOrderedStatic ActualEMCarrierOwn ActualDressedFrequencyHalf
open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] zeroClockClearing zeroClockFrequencyEMFraction zeroClockFrequencyDenominator
  emCommonSpectralRoots emInsertion emPhysicalLeftPoleCoefficient emFullRowPoleOrder
  emVisiblePairedClockEnergy emVisiblePairedHigherEnergy emVisiblePairedSourceInput
  emVisiblePairedAnalyticDebt emVisibleClockGraphPrice emVisibleEnergyNormalizedResidue
  correctedPhysicalClock correctedPhysicalClockJet emFullPhysicalResidue emRightResidueDefect
  emCompleteLeftDefect PencilClockBalanced EMColumnsClockFinite
  frequencyClockDeterminant FrequencyClockFinite frequencyClockEMNumerator fullClockEMColumn
  frequencyClockOrder correctedEMTensor correctedEMColumn zeroClockFrequencyEMRead zeroClockEMColumnRead
  frequencyResponsePencil sourceTangentPhysicalSpatialJet emVisiblePairedSpatialEnergy

structure EMActualSpectralObservation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) where
  complete : EMGeneratedSpectralBranch event eps n eps_ne a c
  full : FullEMZeroClockMode event eps n c.val.1 c.val.2 a.val
  actual_principal_return : ∀omega : ℝ,
    (zeroClockFrequencyDenominator event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0 →
    (omega : ℂ)≠physicalFrequencyPole eps a.val →
    (rootRemainder (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val).eval
      ((omega/eps^2 : ℝ) : ℂ)≠0 →
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps (omega/eps^2) sigma n c.val.1 c.val.2)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((∑k∈Finset.range (poleOrder (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val),
        clockPrincipalCoefficient (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val (eps^2 : ℂ) k*
          ((omega : ℂ)-physicalFrequencyPole eps a.val)^k/
            ((omega : ℂ)-physicalFrequencyPole eps a.val)^poleOrder (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val)+
        (analyticNumerator (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val).eval ((omega/eps^2 : ℝ) : ℂ)/
          (rootRemainder (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val).eval ((omega/eps^2 : ℝ) : ℂ)))

def sourceEMActualSpectralObservation (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (tensor : EMTensorClockFinite event eps n)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) :
    EMActualSpectralObservation event eps n eps_ne a c :=
  ⟨sourceEMGeneratedSpectrum event eps n eps_ne a c,
    sourceFullEMZeroClockMode event eps n c.val.1 c.val.2 a.val balanced finite c.property,
    fun omega regular away tail => actual_zero_clock_frequency_principal event eps omega n c.val.1 c.val.2
      a.val eps_ne regular (tensor c.val.1 c.val.2) c.property away tail⟩

/-- The chart is selected by the original source price; an unpaid price remains an output. -/
inductive EMSourceClockPriceChart (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : Type
  | resolved (priced : emVisibleClockGraphPrice event eps s n mu nu r<‖emVisiblePairedSourceInput event eps s n mu nu r‖)
      (nonzero : emVisiblePairedClockEnergy event eps s n mu nu r≠0)
      (unit : dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
        (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥ
          emVisibleEnergyNormalizedResidue event eps s n mu nu r)=1)
  | unresolved (excess : ‖emVisiblePairedSourceInput event eps s n mu nu r‖≤emVisibleClockGraphPrice event eps s n mu nu r)

def emRealSpectralIndex (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) : ℕ :=
  emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root

structure EMSourceRealEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) where
  left_defect : (correctedPhysicalClock event eps (sourceFrequency eps s) n).transpose*ᵥ
    emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) (emRealSpectralIndex event eps s n mu nu eps_ne root)=
      -emCompleteLeftDefect event eps n mu (s : ℂ) (emRealSpectralIndex event eps s n mu nu eps_ne root)
  right_defect : correctedPhysicalClock event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)=
    -emRightResidueDefect event eps n nu (s : ℂ)
  balance : let r := emRealSpectralIndex event eps s n mu nu eps_ne root
    emVisiblePairedClockEnergy event eps s n mu nu r+emVisiblePairedHigherEnergy event eps s n mu nu r=
      emVisiblePairedSourceInput event eps s n mu nu r+emVisiblePairedAnalyticDebt event eps s n mu nu r
  complete_nonzero : let r := emRealSpectralIndex event eps s n mu nu eps_ne root
    emVisiblePairedClockEnergy event eps s n mu nu r+emVisiblePairedHigherEnergy event eps s n mu nu r-
      emVisiblePairedAnalyticDebt event eps s n mu nu r=emVisiblePairedSourceInput event eps s n mu nu r ∧
      emVisiblePairedSourceInput event eps s n mu nu r≠0
  whole_unit : let r := emRealSpectralIndex event eps s n mu nu eps_ne root
    emVisiblePairedClockEnergy event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r+
      emVisiblePairedHigherEnergy event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r-
        emVisiblePairedAnalyticDebt event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r=1
  graph_bound : let r := emRealSpectralIndex event eps s n mu nu eps_ne root
    ‖emVisiblePairedSourceInput event eps s n mu nu r‖-emVisibleClockGraphPrice event eps s n mu nu r≤
      ‖emVisiblePairedClockEnergy event eps s n mu nu r‖
  graph_chart : EMSourceClockPriceChart event eps s n mu nu (emRealSpectralIndex event eps s n mu nu eps_ne root)

def sourceEMRealEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    EMSourceRealEnergy event eps s n mu nu eps_ne root := by
  classical
  have selected := actual_em_visible_left_selector_spec event eps n mu nu (s : ℂ) eps_ne root
  have chart : EMSourceClockPriceChart event eps s n mu nu (emRealSpectralIndex event eps s n mu nu eps_ne root) := by
    by_cases priced : emVisibleClockGraphPrice event eps s n mu nu (emRealSpectralIndex event eps s n mu nu eps_ne root)<
      ‖emVisiblePairedSourceInput event eps s n mu nu (emRealSpectralIndex event eps s n mu nu eps_ne root)‖
    · exact .resolved priced
        (actual_em_visible_clock_graph_nondegenerate event eps s n mu nu eps_ne balanced finite regular root priced)
        (actual_em_visible_clock_unit_from_price event eps s n mu nu eps_ne balanced finite regular root priced)
    · exact .unresolved (le_of_not_gt priced)
  exact {
    left_defect := actual_em_complete_left_defect event eps s n mu nu eps_ne regular root _ selected.1
    right_defect := actual_em_right_residue_defect event eps s n mu nu eps_ne balanced finite regular root
    balance := actual_em_visible_paired_energy_balance event eps s n mu nu eps_ne balanced finite regular root _ selected.1
    complete_nonzero := actual_em_visible_whole_energy_nonzero event eps s n mu nu eps_ne balanced finite regular root
    whole_unit := actual_em_visible_whole_energy_unit event eps s n mu nu eps_ne balanced finite regular root
    graph_bound := actual_em_visible_clock_graph_bound event eps s n mu nu eps_ne balanced finite regular root
    graph_chart := chart
  }

private theorem real_pole_cast (a : ℂ) (real : a.im=0) : (a.re : ℂ)=a := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · simpa only [Complex.ofReal_im] using real.symm

theorem emSpectralRealRoot (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) (real : a.val.im=0) :
    (a.val.re : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) := by
  rw [real_pole_cast a.val real]
  exact c.property

theorem source_em_spectral_real_selector (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) :
    emRealSpectralIndex event eps a.val.re n c.val.1 c.val.2 eps_ne (emSpectralRealRoot event eps n a c real)=
      emSpectralLeftIndex event eps n eps_ne a c := by
  simp only [emRealSpectralIndex,emSpectralLeftIndex,real_pole_cast a.val real]

theorem source_em_spectral_real_frequency (eps : ℝ) (a : ℂ) (real : a.im=0) :
    physicalFrequencyPole eps a=(sourceFrequency eps a.re : ℂ) := by
  rw [physicalFrequencyPole,sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow,real_pole_cast a real]

/-- Moving modes are consumers of the generated spectrum; both original derivative debts remain. -/
theorem source_em_spectral_moving_clock (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (regular : (zeroClockClearing event eps n).eval a.val≠0)
    (l v : ℝ→Fin 289→ℂ) (l' v' : Fin 289→ℂ)
    (leftPoint : l (sourceFrequency eps a.val.re)=
      emPhysicalLeftPoleCoefficient event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c))
    (rightPoint : v (sourceFrequency eps a.val.re)=emFullPhysicalResidue event eps n c.val.2 a.val)
    (left : HasDerivAt l l' (sourceFrequency eps a.val.re))
    (right : HasDerivAt v v' (sourceFrequency eps a.val.re)) :
    HasDerivAt (fun omega => dotProduct (l omega) (correctedPhysicalClock event eps omega n*ᵥv omega))
      (emVisiblePairedClockEnergy event eps a.val.re n c.val.1 c.val.2 (emSpectralLeftIndex event eps n eps_ne a c)-
        dotProduct l' (emRightResidueDefect event eps n c.val.2 a.val)-
          dotProduct (emCompleteLeftDefect event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c)) v')
      (sourceFrequency eps a.val.re) := by
  have generated := sourceEMGeneratedSpectrum event eps n eps_ne a c
  have paid := actual_em_visible_moving_clock_read event eps a.val.re n c.val.1 c.val.2 eps_ne balanced finite
    (by rwa [real_pole_cast a.val real]) (emSpectralRealRoot event eps n a c real)
    (emSpectralLeftIndex event eps n eps_ne a c) (by simpa only [real_pole_cast a.val real] using generated.left_lower)
    l v l' v' (by simpa only [real_pole_cast a.val real] using leftPoint)
    (by simpa only [real_pole_cast a.val real] using rightPoint) left right
  simpa only [real_pole_cast a.val real] using paid

theorem source_em_spectral_moving_spatial (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (regular : (zeroClockClearing event eps n).eval a.val≠0)
    (spatialRegular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0
      ((sourceFrequency eps a.val.re/eps^2 : ℝ) : ℂ)≠0)
    (l v : ℝ→Fin 289→ℂ) (l' v' : Fin 289→ℂ)
    (leftPoint : l 0=emPhysicalLeftPoleCoefficient event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c))
    (rightPoint : v 0=emFullPhysicalResidue event eps n c.val.2 a.val)
    (left : HasDerivAt l l' 0) (right : HasDerivAt v v' 0) :
    HasDerivAt (fun t => dotProduct (l t)
      (correctedPhysicalClock event eps (sourceFrequency eps a.val.re) (sourceTangentMomentum n delta t)*ᵥv t))
      (-(eps^2 : ℂ)*emVisiblePairedSpatialEnergy event eps a.val.re n delta c.val.1 c.val.2 (emSpectralLeftIndex event eps n eps_ne a c)-
        dotProduct l' (emRightResidueDefect event eps n c.val.2 a.val)-
          dotProduct (emCompleteLeftDefect event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c)) v') 0 := by
  have generated := sourceEMGeneratedSpectrum event eps n eps_ne a c
  have paid := actual_em_visible_moving_spatial_read event eps a.val.re n delta c.val.1 c.val.2 eps_ne balanced finite
    (by rwa [real_pole_cast a.val real]) spatialRegular (emSpectralRealRoot event eps n a c real)
    (emSpectralLeftIndex event eps n eps_ne a c) (by simpa only [real_pole_cast a.val real] using generated.left_lower)
    l v l' v' (by simpa only [real_pole_cast a.val real] using leftPoint)
    (by simpa only [real_pole_cast a.val real] using rightPoint) left right
  simpa only [real_pole_cast a.val real] using paid

inductive EMSourceSpectralBranchReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) : Type
  | nonreal (imaginary : a.val.im≠0) (observation : EMActualSpectralObservation event eps n eps_ne a c)
  | clearingFailure (real : a.val.im=0) (zero : (zeroClockClearing event eps n).eval a.val=0)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)
  | physical (real : a.val.im=0) (regular : (zeroClockClearing event eps n).eval a.val≠0)
      (observation : EMActualSpectralObservation event eps n eps_ne a c)
      (energy : EMSourceRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne (emSpectralRealRoot event eps n a c real))

def sourceEMSpectralBranchReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (tensor : EMTensorClockFinite event eps n)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) :
    EMSourceSpectralBranchReturn event eps n eps_ne a c := by
  classical
  let observation := sourceEMActualSpectralObservation event eps n eps_ne tensor balanced finite a c
  by_cases real : a.val.im=0
  · by_cases regular : (zeroClockClearing event eps n).eval a.val≠0
    · exact .physical real regular observation
        (sourceEMRealEnergy event eps a.val.re n c.val.1 c.val.2 eps_ne balanced finite
          (by rwa [real_pole_cast a.val real]) (emSpectralRealRoot event eps n a c real))
    · exact .clearingFailure real (not_ne_iff.mp regular) observation
  · exact .nonreal real observation

/-- Every original reduced-denominator zero is generated inside the same complete spectrum, before a consumer selects it. -/
theorem source_em_original_denominator_coverage (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) : ∀mu nu : Fin 4, ∀z : ℂ,
    (zeroClockFrequencyEMFraction event eps n mu nu).denom.eval z=0 →
    ∃a : EMSourcePole event eps n, ∃c : EMSourceVisibleChannel event eps n a,
      a.val=z ∧ c.val=(mu,nu) ∧
      dotProduct (fun i => emInsertion i c.val.2)
        (emPhysicalLeftPoleCoefficient event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c))≠0 := by
  intro mu nu z zero
  have root := (visible_root_iff (zeroClockFrequencyEMFraction event eps n mu nu) z).mpr zero
  let a : EMSourcePole event eps n := ⟨z,(source_em_complete_spectral_coverage event eps n z).mpr ⟨mu,nu,root⟩⟩
  let c : EMSourceVisibleChannel event eps n a := ⟨(mu,nu),root⟩
  exact ⟨a,c,rfl,rfl,(sourceEMGeneratedSpectrum event eps n eps_ne a c).detector_nonzero⟩

/-- Total source disposition retains every original clock failure and every generated visible branch. -/
inductive EMCompleteSourceSpectrumReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Type
  | zeroScale (zero : eps=0)
  | singular (eps_ne : eps≠0) (zero : frequencyClockDeterminant event eps n=0)
  | tensorClock (eps_ne : eps≠0) (nonzero : frequencyClockDeterminant event eps n≠0)
      (failure : ¬EMTensorClockFinite event eps n)
      (pole : ∃mu nu, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (frequencyClockEMNumerator event eps n mu nu))
          (clockSpecialize s (frequencyClockDeterminant event eps n))) 0)
  | columnClock (eps_ne : eps≠0) (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (failure : ¬EMColumnsClockFinite event eps n)
      (pole : ∃nu i, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockEMColumn event eps n nu i))
          (clockSpecialize s (frequencyClockDeterminant event eps n))) 0)
  | thresholdClock (eps_ne : eps≠0) (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (columns : EMColumnsClockFinite event eps n)
      (failure : ¬PencilClockBalanced event eps n)
      (pole : ∃i j, ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
        0<poleOrder (readFraction (clockSpecialize s (fullClockPencil event eps n i j))
          (clockSpecialize s (fullClockClearing event eps n))) 0)
  | realized (eps_ne : eps≠0) (nonzero : frequencyClockDeterminant event eps n≠0)
      (tensor : EMTensorClockFinite event eps n) (columns : EMColumnsClockFinite event eps n)
      (balanced : PencilClockBalanced event eps n)
      (branches : ∀a : EMSourcePole event eps n, ∀c : EMSourceVisibleChannel event eps n a,
        EMSourceSpectralBranchReturn event eps n eps_ne a c)
      (column_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        ∀nu : Fin 4, Tendsto (fun sigma : ℝ => correctedEMColumn event eps s sigma n nu)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMColumnRead event eps s n nu)))
      (tensor_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyEMRead event eps s n)))
      (pencil_return : ∀s : ℝ, (zeroClockClearing event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => frequencyResponsePencil event ((eps^2 : ℝ) • n)
          (frequencyRay eps s n) (dampedFourierClock (sourceFrequency eps s) sigma))
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockThresholdPencil event eps s n)))

def sourceEMCompleteSpectrumReturn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    EMCompleteSourceSpectrumReturn event eps n := by
  classical
  by_cases zero : eps=0
  · exact .zeroScale zero
  · cases sourceEMColumnsClockReturn event eps n with
    | singular failed => exact .singular zero failed
    | tensorClock nonzero failure pole => exact .tensorClock zero nonzero failure pole
    | columnClock nonzero tensor failure pole => exact .columnClock zero nonzero tensor failure pole
    | thresholdClock nonzero tensor columns failure pole => exact .thresholdClock zero nonzero tensor columns failure pole
    | realized nonzero tensor columns balanced _mode column_return tensor_return pencil_return =>
      exact .realized zero nonzero tensor columns balanced
        (sourceEMSpectralBranchReturn event eps n zero tensor balanced columns)
        column_return tensor_return pencil_return

end LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
