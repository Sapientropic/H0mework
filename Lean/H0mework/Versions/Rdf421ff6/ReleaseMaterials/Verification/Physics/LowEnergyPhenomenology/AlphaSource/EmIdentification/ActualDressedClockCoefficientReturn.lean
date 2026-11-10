import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRClockCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedOrderedStatic
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualCompositeFieldCurrent Filter Set
open scoped Matrix Topology
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

private theorem specialized_nonzero (D : (ℂ[X])[X]) (m : ℕ) (eps : ℝ)
    (regular : (D.coeff m).eval (eps : ℂ)≠0) : clockSpecialize eps D≠0 := by
  intro zero
  have coefficient := congrArg (fun P : ℂ[X] => P.coeff m) zero
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero] at coefficient
  exact regular coefficient

private theorem coefficient_after_factor (Q : (ℂ[X])[X]) (m : ℕ) (eps : ℝ) :
    (clockSpecialize eps Q).eval 0=((X^m*Q).coeff m).eval (eps : ℂ) := by
  have coefficient : (X^m*Q).coeff m=Q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul Q m 0
  rw [coefficient,← coeff_zero_eq_eval_zero]
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map]
  rfl

private theorem canceled_clock_read (N D : (ℂ[X])[X]) (m : ℕ) (eps : ℝ)
    (nFactor : X^m∣N) (dFactor : X^m∣D) (regular : (D.coeff m).eval (eps : ℂ)≠0) :
    let R := readFraction (clockSpecialize eps N) (clockSpecialize eps D)
    poleOrder R 0=0 ∧ leadingPoleCoefficient R 0=(N.coeff m).eval (eps : ℂ)/(D.coeff m).eval (eps : ℂ) := by
  dsimp only
  obtain ⟨Nq,nEq⟩ := nFactor
  obtain ⟨Dq,dEq⟩ := dFactor
  have nValue := coefficient_after_factor Nq m eps
  have dValue := coefficient_after_factor Dq m eps
  rw [← nEq] at nValue
  rw [← dEq] at dValue
  have qRegular : (clockSpecialize eps Dq).eval 0≠0 := by rw [dValue]; exact regular
  have ratio : readFraction (clockSpecialize eps N) (clockSpecialize eps D)=
      readFraction (clockSpecialize eps Nq) (clockSpecialize eps Dq) := by
    rw [nEq,dEq]
    simp only [map_mul,map_pow,clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_X,readFraction]
    exact mul_div_mul_left _ _ (pow_ne_zero m (RatFunc.algebraMap_ne_zero (X_ne_zero : (X : ℂ[X])≠0)))
  let R := readFraction (clockSpecialize eps Nq) (clockSpecialize eps Dq)
  have rRegular : R.denom.eval 0≠0 := reduced_denominator_at_regular _ _ 0 qRegular
  have zeroOrder : poleOrder R 0=0 := rootMultiplicity_eq_zero rRegular
  rw [ratio]
  refine ⟨zeroOrder,?_⟩
  have leading : leadingPoleCoefficient R 0=R.num.eval 0/R.denom.eval 0 := by
    simp only [leadingPoleCoefficient,rootRemainder,rootPower,zeroOrder,pow_zero,divByMonic_one]
  change leadingPoleCoefficient R 0=_
  rw [leading]
  exact (reduced_read_at_regular _ _ 0 qRegular).trans (by rw [nValue,dValue])

theorem source_clock_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : irClockDeterminant event n≠0) : sourceClockDenominator event n≠0 :=
  coeff_natTrailingDegree_ne_zero.mpr nonzero

theorem source_clock_factor (event : DressedEvent) (n : PhysicalMomentum) :
    X^sourceClockOrder event n∣irClockDeterminant event n :=
  X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)

/-- The original bivariate determinant generates both the spatial punctured chart and the inner original pencil chart. -/
theorem source_ordered_original_chart (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : irClockDeterminant event n≠0) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      (sourceClockDenominator event n).eval (eps : ℂ)≠0 ∧ dampingDeterminant event eps n≠0 ∧
        ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧ correctedDet event eps 0 sigma n≠0 := by
  filter_upwards [source_static_punctured_chart _ (source_clock_denominator_nonzero event n nonzero)] with eps regular
  have specialized := specialized_nonzero _ (sourceClockOrder event n) eps regular
  rw [actual_ir_clock_determinant] at specialized
  exact ⟨regular,specialized,source_damping_original_chart event eps n specialized⟩

def zeroClockEMRead (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => (zeroClockEMFraction event n mu nu).num.eval (eps : ℂ)/
    (zeroClockEMFraction event n mu nu).denom.eval (eps : ℂ)

def zeroClockProbeRead (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  (zeroClockProbeFraction event n pd ps dL dR sL sR).num.eval (eps : ℂ)/
    (zeroClockProbeFraction event n pd ps dL dR sL sR).denom.eval (eps : ℂ)

theorem actual_zero_clock_em_entry (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (regular : (sourceClockDenominator event n).eval (eps : ℂ)≠0) (mu nu : Fin 4)
    (factor : X^sourceClockOrder event n∣irClockEMNumerator event n mu nu) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n mu nu)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n mu nu)) := by
  have paid := canceled_clock_read (irClockEMNumerator event n mu nu) (irClockDeterminant event n)
    (sourceClockOrder event n) eps factor (source_clock_factor event n) regular
  rw [actual_ir_clock_em_numerator,actual_ir_clock_determinant] at paid
  have nonzero := specialized_nonzero _ (sourceClockOrder event n) eps regular
  rw [actual_ir_clock_determinant] at nonzero
  have actual := actual_damping_em_order_return event eps n nonzero mu nu
  have zeroOrder : poleOrder (dampingEMFraction event eps n mu nu) 0=0 := paid.1
  simp only [zeroOrder,pow_zero,one_mul] at actual
  have value : sourceDampingEMValue event eps n mu nu=zeroClockEMRead event eps n mu nu :=
    paid.2.trans (reduced_read_at_regular _ _ (eps : ℂ) regular).symm
  rw [value] at actual
  exact actual

theorem actual_zero_clock_probe (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (regular : (sourceClockDenominator event n).eval (eps : ℂ)≠0)
    (factor : X^sourceClockOrder event n∣irClockProbeNumerator event n pd ps dL dR sL sR) :
    Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR)) := by
  have paid := canceled_clock_read (irClockProbeNumerator event n pd ps dL dR sL sR) (irClockDeterminant event n)
    (sourceClockOrder event n) eps factor (source_clock_factor event n) regular
  rw [actual_ir_clock_probe_numerator,actual_ir_clock_determinant] at paid
  have nonzero := specialized_nonzero _ (sourceClockOrder event n) eps regular
  rw [actual_ir_clock_determinant] at nonzero
  have actual := actual_damping_probe_order_return event eps n pd ps dL dR sL sR nonzero
  have zeroOrder : poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0=0 := paid.1
  simp only [zeroOrder,pow_zero,one_mul] at actual
  have value : sourceDampingProbeValue event eps n pd ps dL dR sL sR=zeroClockProbeRead event eps n pd ps dL dR sL sR :=
    paid.2.trans (reduced_read_at_regular _ _ (eps : ℂ) regular).symm
  rw [value] at actual
  exact actual

end LowEnergy.GaussComposite.ActualDressedOrderedStatic
