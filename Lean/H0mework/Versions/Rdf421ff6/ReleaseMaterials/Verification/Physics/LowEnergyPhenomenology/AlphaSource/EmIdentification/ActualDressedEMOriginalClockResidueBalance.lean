import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMCanonicalPoleCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux LowEnergy.ActualDressedVisiblePole
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] zeroClockPencil zeroClockClearing correctedPhysicalClock correctedPhysicalClockJet emInsertion

private theorem polynomial_series_zero (N d : ℂ[X]) (a : ℂ) :
    PowerSeries.coeff 0 ((taylor a N : PowerSeries ℂ)*(taylor a d : PowerSeries ℂ)⁻¹)=N.eval a/d.eval a := by
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul,Polynomial.constantCoeff_coe,
    PowerSeries.constantCoeff_inv,taylor_coeff_zero,div_eq_mul_inv]

private theorem series_quotient_first (N d : PowerSeries ℂ) (regular : PowerSeries.constantCoeff d≠0) :
    PowerSeries.coeff 1 (N*d⁻¹)=
      (PowerSeries.coeff 1 N*PowerSeries.constantCoeff d-
        PowerSeries.constantCoeff N*PowerSeries.coeff 1 d)/(PowerSeries.constantCoeff d)^2 := by
  have anti : Finset.HasAntidiagonal.antidiagonal (1 : ℕ)={(0,1),(1,0)} := rfl
  have inverseFirst : PowerSeries.coeff 1 d⁻¹=
      -(PowerSeries.constantCoeff d)⁻¹*(PowerSeries.coeff 1 d*(PowerSeries.constantCoeff d)⁻¹) := by
    rw [PowerSeries.coeff_inv]
    simp [anti,PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_inv]
  rw [PowerSeries.coeff_one_mul,inverseFirst,PowerSeries.constantCoeff_inv]
  field_simp [regular]
  ring

private theorem polynomial_series_first (N d : ℂ[X]) (a : ℂ) (regular : d.eval a≠0) :
    PowerSeries.coeff 1 ((taylor a N : PowerSeries ℂ)*(taylor a d : PowerSeries ℂ)⁻¹)=
      (N.derivative.eval a*d.eval a-N.eval a*d.derivative.eval a)/(d.eval a)^2 := by
  have unit : PowerSeries.constantCoeff (taylor a d : PowerSeries ℂ)≠0 := by
    simpa only [Polynomial.constantCoeff_coe,taylor_coeff_zero] using regular
  simpa only [Polynomial.coeff_coe,Polynomial.constantCoeff_coe,taylor_coeff_zero,taylor_coeff_one] using
    series_quotient_first (taylor a N : PowerSeries ℂ) (taylor a d : PowerSeries ℂ) unit

private theorem physical_series_quotient_derivative (N d : ℂ[X]) (eps omega : ℝ)
    (_nonzero : eps≠0) (regular : d.eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun w : ℝ => N.eval ((w/eps^2 : ℝ) : ℂ)/d.eval ((w/eps^2 : ℝ) : ℂ))
      (PowerSeries.coeff 1 ((taylor (((omega/eps^2 : ℝ) : ℂ)) N : PowerSeries ℂ)*
        (taylor (((omega/eps^2 : ℝ) : ℂ)) d : PowerSeries ℂ)⁻¹)/((eps^2 : ℝ) : ℂ)) omega := by
  have ratio := ((N.hasDerivAt ((omega/eps^2 : ℝ) : ℂ)).div
    (d.hasDerivAt ((omega/eps^2 : ℝ) : ℂ)) regular).comp_ofReal
  have scale : HasDerivAt (fun w : ℝ => w/eps^2) (1/eps^2) omega :=
    (hasDerivAt_id omega).div_const (eps^2)
  have chain := ratio.scomp omega scale
  rw [polynomial_series_first N d _ regular]
  have coefficient : (1/eps^2 : ℝ) •
      ((N.derivative.eval ((omega/eps^2 : ℝ) : ℂ)*d.eval ((omega/eps^2 : ℝ) : ℂ)-
        N.eval ((omega/eps^2 : ℝ) : ℂ)*d.derivative.eval ((omega/eps^2 : ℝ) : ℂ))/
          (d.eval ((omega/eps^2 : ℝ) : ℂ))^2)=
      ((N.derivative.eval ((omega/eps^2 : ℝ) : ℂ)*d.eval ((omega/eps^2 : ℝ) : ℂ)-
        N.eval ((omega/eps^2 : ℝ) : ℂ)*d.derivative.eval ((omega/eps^2 : ℝ) : ℂ))/
          (d.eval ((omega/eps^2 : ℝ) : ℂ))^2)/((eps^2 : ℝ) : ℂ) := by
    rw [Complex.real_smul]
    simp only [Complex.ofReal_div,Complex.ofReal_one]
    ring
  rw [coefficient] at chain
  simpa only [Function.comp_def,Pi.div_apply] using chain

private theorem frequency_point (eps s : ℝ) (nonzero : eps≠0) : sourceFrequency eps s/eps^2=s := by
  unfold sourceFrequency
  field_simp [pow_ne_zero 2 nonzero]

theorem actual_em_physical_pole_clock_zero (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0) :
    emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) 0=
      correctedPhysicalClock event eps (sourceFrequency eps s) n := by
  have point := frequency_point eps s nonzero
  have same := actual_corrected_physical_threshold event eps (sourceFrequency eps s) n nonzero
    (by simpa only [point] using regular)
  rw [point] at same
  funext i j
  have value := polynomial_series_zero (zeroClockPencil event eps n i j) (zeroClockClearing event eps n) (s : ℂ)
  have original := congrFun (congrFun same i) j
  simpa only [emPhysicalCorrectedPoleCoefficient,emCorrectedPoleCoefficient,emCorrectedPoleSeries,pow_zero,div_one]
    using value.trans original.symm

/-- The first source coefficient is the already-paid derivative of the actual physical corrected matrix. -/
theorem actual_em_physical_pole_clock_first (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (nonzero : eps≠0)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0) :
    emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) 1=
      correctedPhysicalClockJet event eps (sourceFrequency eps s) n := by
  have point := frequency_point eps s nonzero
  have atPoint : (zeroClockClearing event eps n).eval ((sourceFrequency eps s/eps^2 : ℝ) : ℂ)≠0 := by
    simpa only [point] using regular
  have original := actual_corrected_physical_clock_derivative event eps (sourceFrequency eps s) n nonzero atPoint
  have continuous : Continuous (fun w : ℝ => (zeroClockClearing event eps n).eval ((w/eps^2 : ℝ) : ℂ)) := by fun_prop
  have chart : ∀ᶠ w : ℝ in 𝓝 (sourceFrequency eps s),
      (zeroClockClearing event eps n).eval ((w/eps^2 : ℝ) : ℂ)≠0 :=
    (continuous.tendsto _).eventually (eventually_ne_nhds atPoint)
  funext i j
  have ratio := physical_series_quotient_derivative (zeroClockPencil event eps n i j)
    (zeroClockClearing event eps n) eps (sourceFrequency eps s) nonzero atPoint
  have same : (fun w : ℝ => correctedPhysicalClock event eps w n i j)=ᶠ[𝓝 (sourceFrequency eps s)]
      (fun w : ℝ => (zeroClockPencil event eps n i j).eval ((w/eps^2 : ℝ) : ℂ)/
        (zeroClockClearing event eps n).eval ((w/eps^2 : ℝ) : ℂ)) := by
    filter_upwards [chart] with w regularW
    exact congrFun (congrFun (actual_corrected_physical_threshold event eps w n nonzero regularW) i) j
  have entry := hasDerivAt_pi.mp (hasDerivAt_pi.mp original i) j
  have paid := (ratio.congr_of_eventuallyEq same).unique entry
  simpa only [emPhysicalCorrectedPoleCoefficient,emCorrectedPoleCoefficient,emCorrectedPoleSeries,pow_one,point] using paid

private theorem separate_first_two {A : Type*} [AddCommMonoid A] (f : ℕ → A) (q : ℕ) (positive : 0<q) :
    (∑r∈Finset.range (q+1), f r)=f 0+f 1+∑r∈Finset.range (q-1), f (r+2) := by
  have count : q+1=2+(q-1) := by omega
  rw [count,Finset.sum_range_add]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.add_comm]

private theorem separated_pole_balance {ι : Type*} [Fintype ι]
    (P : ℕ → Matrix ι ι ℂ) (V : ℕ → ι → ℂ) (E : ι → ℂ) (q : ℕ) (positive : 0<q)
    (paid : ∀i, (∑j, ∑p∈Finset.HasAntidiagonal.antidiagonal q, P p.1 i j*V p.2 j)=E i) :
    P 0*ᵥV q+P 1*ᵥV (q-1)+
      (∑r∈Finset.range (q-1), P (r+2)*ᵥV (q-(r+2)))=E := by
  have equation : (∑r∈Finset.range (q+1), P r*ᵥV (q-r))=E := by
    funext i
    have value := paid i
    rw [Finset.sum_comm,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at value
    simpa only [Finset.sum_apply,Matrix.mulVec,dotProduct] using value
  rw [separate_first_two _ q positive] at equation
  simpa only [Nat.sub_zero] using equation

/-- Actual physical derivative times canonical residue is paid inside the complete mixed field balance. -/
theorem actual_em_original_physical_residue_balance (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (nonzero : eps≠0)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (clearingRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    correctedPhysicalClock event eps (sourceFrequency eps s) n*ᵥ
      (fun i => (emFullAnalyticColumnNumerator event eps n nu (s : ℂ) i).eval (s : ℂ)/
        (emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ))+
      correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)+
      (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
        emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (r+2)*ᵥ
          emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ)
            (emFullColumnPoleOrder event eps n nu (s : ℂ)-(r+2)))=
      (fun i => emInsertion i nu) := by
  have paid := separated_pole_balance
    (emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ))
    (emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ))
    (fun i => emInsertion i nu) (emFullColumnPoleOrder event eps n nu (s : ℂ))
    (source_em_full_pole_order_positive event eps n mu nu (s : ℂ) root)
    (actual_em_physical_full_pole_balance event eps n mu nu (s : ℂ) nonzero balanced finite clearingRegular root)
  rw [actual_em_physical_pole_clock_zero event eps s n nonzero clearingRegular,
    actual_em_physical_pole_clock_first event eps s n nonzero clearingRegular,
    source_em_physical_canonical_analytic_coefficient event eps n mu nu (s : ℂ) nonzero root,
    source_em_physical_canonical_residue event eps n mu nu (s : ℂ) nonzero root] at paid
  exact paid

end LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
