import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMCommonSpectralPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMTensorClock ActualDressedEMPolePairEnergy
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux ActualDressedEMPhysicalResidueFlux
open ActualDressedEMVisiblePoleTransport ActualEMCarrierOwn
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emInsertion zeroClockPencil zeroClockClearing
  emFullRowPoleOrder emFullColumnPoleOrder emCancelledFullColumn emColumnDenominatorTail
  emCommonSpectralRoots zeroClockFrequencyEMFraction emPhysicalLeftPoleCoefficient
  emNormalizedFullPoleMode emFullPrincipalPolynomial emFullAnalyticColumnNumerator
  emNormalizedPoleColumnSeries emPhysicalNormalizedPoleColumnCoefficient emPhysicalPrincipalCoefficient
  emCorrectedPoleSeries emLeftPoleSeries emLeftClockDefectSeries emPhysicalCorrectedPoleCoefficient
  emPhysicalLeftClockDefectCoefficient PencilClockBalanced EMColumnsClockFinite

def emSpectralLeftIndex (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (eps_ne : eps≠0)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) : ℕ :=
  emVisibleLeftSelector event eps n c.val.1 c.val.2 a.val eps_ne c.property

/-- A fibre preserves the observed scalar, the complete vector and both original inhomogeneous chains. -/
structure EMGeneratedSpectralBranch (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) where
  observed : FrequencyPrincipal eps (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) a.val
  observed_generated : observed=sourceFrequencyPrincipal eps
    (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) ⟨a.val,c.property⟩
  left_lower : emSpectralLeftIndex event eps n eps_ne a c<emFullRowPoleOrder event eps n c.val.1 a.val
  detector_nonzero : dotProduct (fun i => emInsertion i c.val.2)
    (emPhysicalLeftPoleCoefficient event eps n c.val.1 a.val (emSpectralLeftIndex event eps n eps_ne a c))≠0
  full_mode_nonzero : emNormalizedFullPoleMode event eps n c.val.2 a.val≠0
  tail_regular : (emColumnDenominatorTail event eps n a.val).eval a.val≠0
  principal_analytic : emCancelledFullColumn event eps n c.val.2 a.val=
    emColumnDenominatorTail event eps n a.val • emFullPrincipalPolynomial event eps n c.val.2 a.val+
      (X-C a.val)^emFullColumnPoleOrder event eps n c.val.2 a.val • emFullAnalyticColumnNumerator event eps n c.val.2 a.val
  complete_series : ∀i : Fin 289, emNormalizedPoleColumnSeries event eps n c.val.2 a.val i=
    (taylor a.val (emFullPrincipalPolynomial event eps n c.val.2 a.val i) : PowerSeries ℂ)+
      (PowerSeries.X : PowerSeries ℂ)^emFullColumnPoleOrder event eps n c.val.2 a.val*
        ((taylor a.val (emFullAnalyticColumnNumerator event eps n c.val.2 a.val i) : PowerSeries ℂ)*
          (taylor a.val (emColumnDenominatorTail event eps n a.val) : PowerSeries ℂ)⁻¹)
  all_principal_coefficients : ∀r : ℕ, r<emFullColumnPoleOrder event eps n c.val.2 a.val →
    emPhysicalNormalizedPoleColumnCoefficient event eps n c.val.2 a.val r=
      emPhysicalPrincipalCoefficient event eps n c.val.2 a.val r
  analytic_coefficient : emPhysicalNormalizedPoleColumnCoefficient event eps n c.val.2 a.val
    (emFullColumnPoleOrder event eps n c.val.2 a.val)=
      (fun i => (emFullAnalyticColumnNumerator event eps n c.val.2 a.val i).eval a.val/
        (emColumnDenominatorTail event eps n a.val).eval a.val)
  left_series : (zeroClockClearing event eps n).eval a.val≠0 →
    (emCorrectedPoleSeries event eps n a.val).transpose*ᵥemLeftPoleSeries event eps n c.val.1 a.val+
      emLeftClockDefectSeries event eps n c.val.1 a.val=
      (PowerSeries.X : PowerSeries ℂ)^emFullRowPoleOrder event eps n c.val.1 a.val •
        (fun i => PowerSeries.C (emInsertion i c.val.1))
  all_left_chain : (zeroClockClearing event eps n).eval a.val≠0 →
    ∀k : ℕ, k<emFullRowPoleOrder event eps n c.val.1 a.val → ∀i : Fin 289,
      (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
        emPhysicalCorrectedPoleCoefficient event eps n a.val p.1 j i*
          emPhysicalLeftPoleCoefficient event eps n c.val.1 a.val p.2 j)+
        emPhysicalLeftClockDefectCoefficient event eps n c.val.1 a.val k i=0
  right_series : PencilClockBalanced event eps n → EMColumnsClockFinite event eps n →
    (zeroClockClearing event eps n).eval a.val≠0 →
    emCorrectedPoleSeries event eps n a.val*ᵥemNormalizedPoleColumnSeries event eps n c.val.2 a.val=
      (PowerSeries.X : PowerSeries ℂ)^emFullColumnPoleOrder event eps n c.val.2 a.val •
        (fun i => PowerSeries.C (emInsertion i c.val.2))
  all_right_chain : PencilClockBalanced event eps n → EMColumnsClockFinite event eps n →
    (zeroClockClearing event eps n).eval a.val≠0 →
    ∀k : ℕ, k<emFullColumnPoleOrder event eps n c.val.2 a.val → ∀i : Fin 289,
      (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
        emPhysicalCorrectedPoleCoefficient event eps n a.val p.1 i j*
          emPhysicalNormalizedPoleColumnCoefficient event eps n c.val.2 a.val p.2 j)=0
  complete_forcing : PencilClockBalanced event eps n → EMColumnsClockFinite event eps n →
    (zeroClockClearing event eps n).eval a.val≠0 → ∀i : Fin 289,
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal (emFullColumnPoleOrder event eps n c.val.2 a.val),
      emPhysicalCorrectedPoleCoefficient event eps n a.val p.1 i j*
        emPhysicalNormalizedPoleColumnCoefficient event eps n c.val.2 a.val p.2 j)=emInsertion i c.val.2

def sourceEMGeneratedSpectralBranch (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (eps_ne : eps≠0)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a) :
    EMGeneratedSpectralBranch event eps n eps_ne a c := by
  have selected := actual_em_visible_left_selector_spec event eps n c.val.1 c.val.2 a.val eps_ne c.property
  exact {
    observed := sourceFrequencyPrincipal eps (zeroClockFrequencyEMFraction event eps n c.val.1 c.val.2) ⟨a.val,c.property⟩
    observed_generated := rfl
    left_lower := selected.1
    detector_nonzero := selected.2
    full_mode_nonzero := source_em_normalized_full_pole_nonzero event eps n c.val.1 c.val.2 a.val c.property
    tail_regular := source_em_denominator_tail_nonzero event eps n c.val.1 c.val.2 a.val c.property
    principal_analytic := source_em_full_principal_decomposition event eps n c.val.1 c.val.2 a.val c.property
    complete_series := source_em_normalized_principal_series event eps n c.val.1 c.val.2 a.val c.property
    all_principal_coefficients := source_em_physical_canonical_principal_coefficient event eps n c.val.1 c.val.2 a.val eps_ne c.property
    analytic_coefficient := source_em_physical_canonical_analytic_coefficient event eps n c.val.1 c.val.2 a.val eps_ne c.property
    left_series := fun regular => actual_em_original_left_pole_series event eps n c.val.1 c.val.2 a.val regular c.property
    all_left_chain := fun regular => actual_em_physical_lower_left_chain event eps n c.val.1 c.val.2 a.val regular c.property
    right_series := fun balanced finite regular => actual_em_normalized_full_pole_series event eps n c.val.1 c.val.2 a.val balanced finite regular c.property
    all_right_chain := fun balanced finite regular => actual_em_physical_lower_pole_chain event eps n c.val.1 c.val.2 a.val balanced finite regular c.property
    complete_forcing := fun balanced finite regular => actual_em_physical_full_pole_balance event eps n c.val.1 c.val.2 a.val eps_ne balanced finite regular c.property
  }

/-- All roots, all visible observers and all multiplicities belong to one fixed source fibre. -/
def sourceEMGeneratedSpectrum (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (eps_ne : eps≠0) :
    ∀a : EMSourcePole event eps n, ∀c : EMSourceVisibleChannel event eps n a,
      EMGeneratedSpectralBranch event eps n eps_ne a c :=
  sourceEMGeneratedSpectralBranch event eps n eps_ne

def emPhysicalSpectralRoots (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Multiset ℂ :=
  (emCommonSpectralRoots event eps n).map (physicalFrequencyPole eps)

theorem source_em_physical_frequency_injective (eps : ℝ) (eps_ne : eps≠0) :
    Function.Injective (physicalFrequencyPole eps) := by
  intro a b h
  exact mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr eps_ne)) h

/-- Physical nonreal poles are kept as nonreal rather than silently interpreted as real energy branches. -/
theorem source_em_physical_frequency_real_iff (eps : ℝ) (eps_ne : eps≠0) (a : ℂ) :
    (physicalFrequencyPole eps a).im=0 ↔ a.im=0 := by
  rw [physicalFrequencyPole,←Complex.ofReal_pow,Complex.mul_im]
  simp only [Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,mul_eq_zero,
    pow_ne_zero 2 eps_ne,false_or]

theorem source_em_physical_spectral_coverage (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (omega : ℂ) : omega∈emPhysicalSpectralRoots event eps n ↔
      ∃a : EMSourcePole event eps n, physicalFrequencyPole eps a.val=omega := by
  rw [emPhysicalSpectralRoots,Multiset.mem_map]
  exact ⟨fun ⟨a,root,eq⟩ => ⟨⟨a,root⟩,eq⟩, fun ⟨a,eq⟩ => ⟨a.val,a.property,eq⟩⟩

theorem source_em_physical_spectral_multiplicity (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : ℂ) :
    (emPhysicalSpectralRoots event eps n).count (physicalFrequencyPole eps a)=
      ∑c : EMChannel, poleOrder (zeroClockFrequencyEMFraction event eps n c.1 c.2) a := by
  classical
  rw [emPhysicalSpectralRoots,Multiset.count_map_eq_count' _ _ (source_em_physical_frequency_injective eps eps_ne),
    source_em_complete_spectral_multiplicity]

end LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
