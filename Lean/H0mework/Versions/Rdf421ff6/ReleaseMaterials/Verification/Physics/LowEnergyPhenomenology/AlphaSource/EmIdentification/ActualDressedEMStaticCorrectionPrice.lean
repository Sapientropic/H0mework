import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMForcedSchurSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb ActualDressedNoetherCoulombUnit
open ActualDressedOrderedStatic ActualDressedEMTensorClock ActualEMCarrierOwn
open Polynomial Filter Set
open scoped Matrix BigOperators Topology

private theorem original_spatial_square_scale (a : ℝ) (n : PhysicalMomentum) :
    spatialSquare (a • n)=a^2*spatialSquare n := by
  simp only [spatialSquare,Pi.smul_apply,smul_eq_mul]
  ring1

/-- Every term is read directly from the same original full corrected source column: Q_R, RB W Q_B, native background and lower couplings. -/
def actualStaticSourceCorrection (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ :=
  -noetherPairScale^2*
    (nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps 0 n)
      (zeroClockQuantumResponse event eps 0 n) (zeroClockEMColumnRead event eps 0 n 0)) 0/
    (8*(Real.pi : ℂ)*(lapse : ℂ)*(spatialSquare n : ℂ))

/-- The complete corrected temporal read is the generated native coefficient plus the explicit source correction, at the actual finite physical momentum. -/
theorem actual_static_noether_coupling_source (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (n_ne : spatialSquare n≠0)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (dRegular : (zeroClockClearing event eps n).eval 0≠0)
    (DRegular : (zeroClockFrequencyDenominator event eps n).eval 0≠0) :
    noetherPairScale^2*(-(eps : ℂ)^4)*zeroClockFrequencyEMRead event eps 0 n 0 0/(4*(Real.pi : ℂ))=
      nativeDirectionalOrderedCoulomb n+actualStaticSourceCorrection event eps n := by
  have source := congrFun (actual_corrected_em_principal_source event eps 0 n 0 balanced finite dRegular DRegular) 0
  have observed := actual_zero_clock_em_column_tensor event eps 0 n 0 0 DRegular finite
  change (emInsertion.transpose*ᵥzeroClockEMColumnRead event eps 0 n 0) 0=
    zeroClockFrequencyEMRead event eps 0 n 0 0 at observed
  simp only [nativePhysicalEMPrincipal,sourceFrequency,mul_zero,Complex.ofReal_zero,
    Matrix.cons_val_zero,zero_mul,add_zero,Pi.add_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] at source
  have square : (spatialSquare ((eps^2 : ℝ) • n) : ℂ)=
      (((eps^2 : ℝ) • n) 0 : ℂ)^2+(((eps^2 : ℝ) • n) 1 : ℂ)^2+(((eps^2 : ℝ) • n) 2 : ℂ)^2 := by
    simp only [spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  simp only [Pi.smul_apply,smul_eq_mul] at square
  rw [← square,original_spatial_square_scale,observed] at source
  unfold actualStaticSourceCorrection nativeDirectionalOrderedCoulomb nativeNoetherCoulomb nativeNoetherResponseWeight
  push_cast at source ⊢
  have ln : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  have nn : (spatialSquare n : ℂ)≠0 := Complex.ofReal_ne_zero.mpr n_ne
  have pn : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  generalize hl : (lapse : ℂ)=L at ln source ⊢
  field_simp [ln,nn,pn] at source ⊢
  linear_combination (-8*noetherPairScale^2)*source

private theorem actual_static_frequency_read (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (DRegular : (zeroClockFrequencyDenominator event eps n).eval 0≠0)
    (finite : EMColumnsClockFinite event eps n)
    (paid : Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n))) :
    zeroClockFrequencyEMRead event eps 0 n 0 0=zeroClockEMRead event eps n 0 0 := by
  have observed := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp paid 0) 0
  exact tendsto_nhds_unique
    (actual_zero_clock_frequency_em_entry event eps 0 n 0 0 DRegular
      (source_em_columns_pay_tensor_factors event eps n finite 0 0)) observed

/-- This is a price of the actual generated Q/background/lower correction, obtained from the unchanged physical order of limits. No correction endpoint is supplied as a premise. -/
theorem actual_static_correction_price_return (event : DressedEvent) (n : PhysicalMomentum)
    (n_ne : spatialSquare n≠0) (nonzero : irClockDeterminant event n≠0)
    (factors : ∀mu nu, X^sourceClockOrder event n∣irClockEMNumerator event n mu nu)
    (bounded : ∀mu nu, LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (columns : ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      PencilClockBalanced event eps n ∧ EMColumnsClockFinite event eps n ∧
      (zeroClockClearing event eps n).eval 0≠0 ∧ (zeroClockFrequencyDenominator event eps n).eval 0≠0) :
    Tendsto (fun eps : ℝ => actualStaticSourceCorrection event eps n)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (actualNativeCoulombCorrection event n)) := by
  have paid := actual_ordered_em_return event n nonzero factors bounded
  have temporal : Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroClockEMRead event eps n 0 0)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceOrderedEMCoefficient event n 0 0)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp paid.2 0) 0
  have normalized := temporal.const_mul (noetherPairScale^2/(4*(Real.pi : ℂ)))
  have target : (noetherPairScale^2/(4*(Real.pi : ℂ)))*sourceOrderedEMCoefficient event n 0 0=
      directionalNoetherCoulombCoefficient event n := by
    simp only [directionalNoetherCoulombCoefficient,noetherTensorCoefficient,Matrix.smul_apply,smul_eq_mul]
    ring1
  rw [target] at normalized
  have price := normalized.sub_const (nativeDirectionalOrderedCoulomb n)
  change Tendsto _ _ (𝓝 (directionalNoetherCoulombCoefficient event n-nativeDirectionalOrderedCoulomb n))
  apply Tendsto.congr' _ price
  filter_upwards [columns,paid.1] with eps chart returned
  have generated := actual_static_noether_coupling_source event eps n n_ne
    chart.1 chart.2.1 chart.2.2.1 chart.2.2.2
  rw [actual_static_frequency_read event eps n chart.2.2.2 chart.2.1 returned] at generated
  linear_combination generated

end LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
