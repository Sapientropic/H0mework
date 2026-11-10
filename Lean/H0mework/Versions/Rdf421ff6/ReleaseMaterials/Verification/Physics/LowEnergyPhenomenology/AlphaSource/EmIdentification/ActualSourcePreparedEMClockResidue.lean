import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMJacobiRow

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMClockResidue
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic
open ActualDressedZeroDamping ActualDressedCorrectedGreen ActualDressedEMTemporal ActualDressedStaticPole
open ActualDressedUniformClockNonzero ActualDressedSylvester
open PreparationVacuumActionFieldLift
open PreparationPhysicalPhaseGaugeRealization
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedEMTwoClockCarrier
open ActualSourcePreparedEMTemporalFreeReturn ActualSourcePreparedEMClockEquation
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedClockReducedPencil
open ActualDressedEMTensorClock
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceFourClockDenominator sourceFourClockClearing
  sourceEMTwoClockResponseNumerator sourceTemporalCorrectedField sourceReducedClockFieldNumerator
  sourceReducedClockDeterminant sourcePreparedEMTemporalPi emTemporalPrice

def sourceEMSpecializedDenominator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  clockSpecialize eps (sourceFourClockDenominator event n)
def sourceEMSpecializedNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (j : Fin 289) : ℂ[X] := clockSpecialize eps (sourceEMTwoClockResponseNumerator event n j)
def sourceEMSpecializedOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℕ :=
  (sourceEMSpecializedDenominator event eps n).natTrailingDegree

def sourceEMFiniteClockDenominator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  sourceEMSpecializedDenominator event eps n /ₘ X^sourceEMSpecializedOrder event eps n
def sourceEMFiniteClockNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (j : Fin 289) : ℂ[X] :=
  sourceEMSpecializedNumerator event eps n j /ₘ X^sourceEMSpecializedOrder event eps n

def sourceEMClockResidue (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (j : Fin 289) : ℂ :=
  (sourceEMSpecializedNumerator event eps n j).coeff (sourceEMSpecializedOrder event eps n) /
    (sourceEMSpecializedDenominator event eps n).coeff (sourceEMSpecializedOrder event eps n)

private theorem clock_X (eps sigma : ℝ) :
    sourceClockEval eps sigma (X : (ℂ[X])[X])=(sigma:ℂ) := by
  simp [sourceClockEval,clockSpecialize]

private theorem specialized_den_eval_nonzero (event : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    (sourceEMSpecializedDenominator event eps n).eval (sigma:ℂ)≠0 := by
  have factor:=congrArg (sourceClockEval eps sigma) (source_four_clock_denominator_factor event n)
  simp only [map_mul,map_pow,clock_X] at factor
  have original : sourceClockEval eps sigma (sourceFourClockClearing event n)≠0 := by
    change (clockSpecialize eps (sourceFourClockClearing event n)).eval (sigma:ℂ)≠0
    rw [sourceFourClockClearing,ir_clock_specialize,damping_slice_eval]
    exact actual_common_ir_denominator_nonzero event n eps sigma 0 positive
  intro zero
  apply original
  rw [←factor]
  change (sigma:ℂ)^sourceFourClockOrder event n *
    (sourceEMSpecializedDenominator event eps n).eval (sigma:ℂ)=0
  rw [zero,mul_zero]

theorem source_em_specialized_denominator_nonzero (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) : sourceEMSpecializedDenominator event eps n≠0 := by
  have paid:=specialized_den_eval_nonzero event eps 1 n (by norm_num)
  exact fun zero=>paid (by rw [zero,eval_zero])

private theorem actual_ratio (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (j : Fin 289) :
    (sourceEMSpecializedNumerator event eps n j).eval (sigma:ℂ) /
      (sourceEMSpecializedDenominator event eps n).eval (sigma:ℂ)=
      (sigma:ℂ)^2*sourcePreparedEMTemporalPi event (eps^2 • n) (sigma:ℂ) j := by
  have clear:=source_em_two_clock_reduced_pi_clear event n eps sigma positive j
  change (sourceEMSpecializedDenominator event eps n).eval (sigma:ℂ)*
    (sigma:ℂ)^2*sourcePreparedEMTemporalPi event (eps^2 • n) (sigma:ℂ) j=
      (sourceEMSpecializedNumerator event eps n j).eval (sigma:ℂ) at clear
  rw [←clear]
  field_simp [specialized_den_eval_nonzero event eps sigma n positive]

/-- Spatial specialization can raise the clock order. The actual sigma-two
row price pays every additional cancellation, including the zero-transfer point. -/
theorem source_em_specialized_numerator_factor (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    X^sourceEMSpecializedOrder event eps n ∣ sourceEMSpecializedNumerator event eps n j := by
  apply bounded_fraction_clock_factor _ _ (2*emTemporalPrice event (eps^2 • n) (fieldUnit j))
    (source_em_specialized_denominator_nonzero event eps n)
  intro sigma positive small
  rw [actual_ratio event eps sigma n positive j,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact source_prepared_em_temporal_pi_two_clock_price event (eps^2 • n) sigma positive small j

private theorem factor_quotient (P : ℂ[X]) (m : ℕ) (factor : X^m∣P) : X^m*(P/ₘX^m)=P := by
  obtain ⟨Q,same⟩:=factor
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow m)]

theorem source_em_finite_clock_denominator_factor (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) :
    X^sourceEMSpecializedOrder event eps n * sourceEMFiniteClockDenominator event eps n=
      sourceEMSpecializedDenominator event eps n :=
  factor_quotient _ _ (X_pow_dvd_iff.mpr (fun _ low=>coeff_eq_zero_of_lt_natTrailingDegree low))

theorem source_em_finite_clock_numerator_factor (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    X^sourceEMSpecializedOrder event eps n * sourceEMFiniteClockNumerator event eps n j=
      sourceEMSpecializedNumerator event eps n j :=
  factor_quotient _ _ (source_em_specialized_numerator_factor event eps n j)

private theorem coefficient_factor (P Q : ℂ[X]) (m : ℕ) (factor : X^m*Q=P) : Q.eval 0=P.coeff m := by
  have coefficient : (X^m*Q).coeff m=Q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul Q m 0
  rw [←factor,coefficient]
  exact Q.coeff_zero_eq_eval_zero.symm

theorem source_em_finite_clock_denominator_origin (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) : (sourceEMFiniteClockDenominator event eps n).eval 0≠0 := by
  rw [coefficient_factor _ _ _ (source_em_finite_clock_denominator_factor event eps n)]
  exact coeff_natTrailingDegree_ne_zero.mpr (source_em_specialized_denominator_nonzero event eps n)

theorem source_em_finite_clock_residue (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    (sourceEMFiniteClockNumerator event eps n j).eval 0 /
      (sourceEMFiniteClockDenominator event eps n).eval 0=sourceEMClockResidue event eps n j := by
  rw [coefficient_factor _ _ _ (source_em_finite_clock_numerator_factor event eps n j),
    coefficient_factor _ _ _ (source_em_finite_clock_denominator_factor event eps n)]
  rfl

/-- The finite source coefficient is generated from the original numerator and
its own nonzero denominator coefficient, without a clock margin or pole-order premise. -/
theorem source_em_two_clock_residue_limit (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    Tendsto (fun sigma : ℝ=>(sigma:ℂ)^2*
      sourcePreparedEMTemporalPi event (eps^2 • n) (sigma:ℂ) j)
      (𝓝[>] 0) (𝓝 (sourceEMClockResidue event eps n j)) := by
  have cn : Continuous (fun sigma : ℝ=>(sourceEMFiniteClockNumerator event eps n j).eval (sigma:ℂ)) := by fun_prop
  have cd : Continuous (fun sigma : ℝ=>(sourceEMFiniteClockDenominator event eps n).eval (sigma:ℂ)) := by fun_prop
  have base:=(cn.continuousAt.div cd.continuousAt
    (source_em_finite_clock_denominator_origin event eps n)).tendsto.mono_left
    (show (𝓝[>] (0:ℝ))≤𝓝 0 from inf_le_left)
  simp only [Pi.div_apply,Complex.ofReal_zero] at base
  rw [source_em_finite_clock_residue] at base
  apply Tendsto.congr' _ base
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  rw [←actual_ratio event eps sigma n positive j,
    ←source_em_finite_clock_numerator_factor event eps n j,
    ←source_em_finite_clock_denominator_factor event eps n,
    eval_mul,eval_mul,eval_pow,eval_X]
  exact (mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne'))).symm

theorem source_em_clock_residue_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    ‖sourceEMClockResidue event eps n j‖≤2*emTemporalPrice event (eps^2 • n) (fieldUnit j) := by
  apply le_of_tendsto (source_em_two_clock_residue_limit event eps n j).norm
  have small : ∀ᶠsigma : ℝ in 𝓝[>] (0:ℝ),sigma<1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin,small] with sigma positive near
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact source_prepared_em_temporal_pi_two_clock_price event (eps^2 • n) sigma positive near.le j

/-- Zero transfer is one actual occurrence regardless of the direction used in
the common bivariate clearing; the generated finite coefficient agrees exactly. -/
theorem source_em_zero_transfer_residue_independent (event : DressedEvent)
    (n n' : PhysicalMomentum) (j : Fin 289) :
    sourceEMClockResidue event 0 n j=sourceEMClockResidue event 0 n' j := by
  have left:=source_em_two_clock_residue_limit event 0 n j
  have right:=source_em_two_clock_residue_limit event 0 n' j
  simp only [zero_pow (by decide : 2≠0),zero_smul] at left right
  exact tendsto_nhds_unique left right

/-- On the original simple-pole branch, the generated coefficient is exactly
the unchanged prepared two-pole EM leading observable, not a new normalization. -/
theorem source_em_clock_residue_original_leading (event : DressedEvent)
    (order : dressedStaticPoleOrder event=1) (n : PhysicalMomentum) (j : Fin 289) :
    sourceEMClockResidue event 0 n j=emTemporalLeading event j := by
  have each (i : Fin 289) : Tendsto
      (fun sigma : ℝ=>((sourcePhaseGaugeField 0) i:ℂ)*((sigma:ℂ)^2*
        dressedStaticPolarization event 0 (sigma:ℂ) i j)) (𝓝[>] 0)
      (𝓝 (((sourcePhaseGaugeField 0) i:ℂ)*dressedStaticPoleLeading event i j)) := by
    have actual:=(dressed_static_pole_leading_limit event i j).const_mul
      ((sourcePhaseGaugeField 0) i:ℂ)
    simpa only [order,mul_one] using actual
  have original : Tendsto
      (fun sigma : ℝ=>∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*((sigma:ℂ)^2*
        dressedStaticPolarization event 0 (sigma:ℂ) i j)) (𝓝[>] 0)
      (𝓝 (emTemporalLeading event j)) := by
    unfold emTemporalLeading
    exact tendsto_finsetSum Finset.univ (fun i _=>each i)
  have same : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^2*
      sourcePreparedEMTemporalPi event 0 (sigma:ℂ) j) (𝓝[>] 0)
      (𝓝 (emTemporalLeading event j)) := by
    apply Tendsto.congr' _ original
    filter_upwards [self_mem_nhdsWithin] with sigma positive
    rw [source_prepared_em_temporal_pi_original event 0 (sigma:ℂ)
      (by simpa only [Complex.ofReal_re,mem_Ioi] using positive) j]
    unfold emTemporalPi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have generated:=source_em_two_clock_residue_limit event 0 n j
  simp only [zero_pow (by decide : 2≠0),zero_smul] at generated
  exact tendsto_nhds_unique generated same

def sourceEMFiniteClockRow (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (j : Fin 289) : ℂ[X] :=
  X*sourceEMFiniteClockDenominator event eps n*clockSpecialize eps (sourceEMClockJacobiRow n j)-
    sourceEMFiniteClockNumerator event eps n j

/-- The actual full row inherits the newly generated specialized cancellation;
no extra determinant, balance or field endpoint is supplied. -/
theorem source_em_specialized_finite_row (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    clockSpecialize eps (sourceEMClockReducedRow event n j)=
      X^sourceEMSpecializedOrder event eps n*sourceEMFiniteClockRow event eps n j := by
  unfold sourceEMClockReducedRow sourceEMFiniteClockRow
  simp only [map_sub,map_mul,clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_X]
  change X*sourceEMSpecializedDenominator event eps n*
    clockSpecialize eps (sourceEMClockJacobiRow n j)-sourceEMSpecializedNumerator event eps n j=_
  rw [←source_em_finite_clock_denominator_factor event eps n,
    ←source_em_finite_clock_numerator_factor event eps n j]
  simp only [clockSpecialize,Polynomial.coe_mapRingHom]
  ring

theorem source_em_finite_clock_row_origin (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289) :
    (sourceEMFiniteClockRow event eps n j).eval 0=
      -(sourceEMFiniteClockNumerator event eps n j).eval 0 := by
  simp only [sourceEMFiniteClockRow,eval_sub,eval_mul,eval_X,zero_mul,zero_sub]

/-- The same original det K and sigma-cubed field numerator consume the finite
EM row after all source-generated clock cancellations. All 289 columns remain. -/
theorem source_em_finite_clock_cofactor_field (event : DressedEvent) (eps sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma)
    (regular : correctedDet event eps 0 sigma n≠0) :
    ∑j : Fin 289,(sourceEMFiniteClockRow event eps n j).eval (sigma:ℂ)*
      sourceReducedClockFieldNumerator event n eps sigma j=
      sourceReducedClockDeterminant event n eps sigma*
        ((sigma:ℂ)*(sourceEMFiniteClockDenominator event eps n).eval (sigma:ℂ)*
          dotProduct sourceTemporalEMForce sourceTemporalEMForce) := by
  have paid:=source_em_clock_reduced_cofactor_field event n eps sigma positive regular
  have row (j : Fin 289) : sourceClockEval eps sigma (sourceEMClockReducedRow event n j)=
      (sigma:ℂ)^sourceEMSpecializedOrder event eps n*
        (sourceEMFiniteClockRow event eps n j).eval (sigma:ℂ) := by
    change (clockSpecialize eps (sourceEMClockReducedRow event n j)).eval (sigma:ℂ)=_
    rw [source_em_specialized_finite_row,eval_mul,eval_pow,eval_X]
  have denominator : sourceClockEval eps sigma (sourceFourClockDenominator event n)=
      (sigma:ℂ)^sourceEMSpecializedOrder event eps n*
        (sourceEMFiniteClockDenominator event eps n).eval (sigma:ℂ) := by
    change (sourceEMSpecializedDenominator event eps n).eval (sigma:ℂ)=_
    rw [←source_em_finite_clock_denominator_factor,eval_mul,eval_pow,eval_X]
  simp_rw [row] at paid
  rw [denominator] at paid
  apply mul_left_cancel₀ (pow_ne_zero (sourceEMSpecializedOrder event eps n)
    (Complex.ofReal_ne_zero.mpr positive.ne'))
  calc
    _=∑j : Fin 289,((sigma:ℂ)^sourceEMSpecializedOrder event eps n*
      (sourceEMFiniteClockRow event eps n j).eval (sigma:ℂ))*
        sourceReducedClockFieldNumerator event n eps sigma j := by
      simp only [Finset.mul_sum,mul_assoc]
    _=sourceReducedClockDeterminant event n eps sigma*
      ((sigma:ℂ)*((sigma:ℂ)^sourceEMSpecializedOrder event eps n*
        (sourceEMFiniteClockDenominator event eps n).eval (sigma:ℂ))*
          dotProduct sourceTemporalEMForce sourceTemporalEMForce) := paid
    _=_ := by ring

end LowEnergy.GaussComposite.ActualSourcePreparedEMClockResidue
