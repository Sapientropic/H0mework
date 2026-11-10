import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMSpatialClockPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMOuterResidue
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMTensorClock
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedEMTwoClockCarrier
open ActualSourcePreparedEMClockResidue ActualSourcePreparedEMSpatialClockPrice
open LowEnergy.ActualDressedVisiblePole LowEnergy.GaussComposite.ActualDressedVisiblePole
open Filter Set
open scoped Topology
attribute [local irreducible] sourceFourClockDenominator sourceFourClockClearing
  sourceEMTwoClockResponseNumerator sourceEMClockResidue sourceEMSpatialClockBudget

def sourceEMOuterDenominator (event : DressedEvent) (n : PhysicalMomentum) : ℂ[X] :=
  (sourceFourClockDenominator event n).coeff 0

def sourceEMOuterNumerator (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) : ℂ[X] :=
  (sourceEMTwoClockResponseNumerator event n j).coeff 0

def sourceEMOuterOrder (event : DressedEvent) (n : PhysicalMomentum) : ℕ :=
  (sourceEMOuterDenominator event n).natTrailingDegree

def sourceEMOuterResidue (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) : ℂ :=
  (sourceEMOuterNumerator event n j).coeff (sourceEMOuterOrder event n) /
    (sourceEMOuterDenominator event n).coeff (sourceEMOuterOrder event n)

/-- The outer denominator comes from the first clock coefficient of the same
original Pi clearing. Its nonzero polynomial is generated before spatial chart selection. -/
theorem source_em_outer_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum) :
    sourceEMOuterDenominator event n≠0 := by
  have specialized:=source_em_specialized_denominator_nonzero event 0 n
  have reduced : sourceFourClockDenominator event n≠0 := by
    intro zero
    apply specialized
    unfold sourceEMSpecializedDenominator
    rw [zero,map_zero]
  have original : sourceFourClockClearing event n≠0 := by
    rw [←source_four_clock_denominator_factor event n]
    exact mul_ne_zero (pow_ne_zero _ (X_ne_zero : (X : (ℂ[X])[X])≠0)) reduced
  have coefficient : (sourceFourClockDenominator event n).coeff 0=
      (sourceFourClockClearing event n).coeff (sourceFourClockOrder event n) := by
    have shifted :
        (X^sourceFourClockOrder event n * sourceFourClockDenominator event n).coeff
          (sourceFourClockOrder event n)=(sourceFourClockDenominator event n).coeff 0 := by
      simpa only [zero_add] using
        coeff_X_pow_mul (sourceFourClockDenominator event n) (sourceFourClockOrder event n) 0
    rw [←source_four_clock_denominator_factor event n]
    exact shifted.symm
  have generated : (sourceFourClockClearing event n).coeff (sourceFourClockOrder event n)≠0 :=
    coeff_natTrailingDegree_ne_zero.mpr original
  exact fun zero=>generated (coefficient.symm.trans zero)

private theorem specialized_zero_coefficient (P : (ℂ[X])[X]) (eps : ℝ) :
    (clockSpecialize eps P).coeff 0=(P.coeff 0).eval (eps:ℂ) := by
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,Polynomial.coe_evalRingHom]

/-- On the source-generated punctured spatial chart, the actual finite clock
residue is the same zero-clock coefficient ratio. The exact epsilon-zero branch remains distinct. -/
theorem source_em_outer_fraction_actual (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (j : Fin 289)
    (regular : (sourceEMOuterDenominator event n).eval (eps:ℂ)≠0) :
    (sourceEMOuterNumerator event n j).eval (eps:ℂ) /
      (sourceEMOuterDenominator event n).eval (eps:ℂ)=sourceEMClockResidue event eps n j := by
  have first : (sourceEMSpecializedDenominator event eps n).coeff 0≠0 := by
    unfold sourceEMSpecializedDenominator
    rw [specialized_zero_coefficient]
    exact regular
  have order : sourceEMSpecializedOrder event eps n=0 :=
    Nat.eq_zero_of_le_zero (natTrailingDegree_le_of_ne_zero first)
  unfold sourceEMClockResidue
  rw [order]
  simp only [sourceEMSpecializedNumerator,sourceEMSpecializedDenominator,specialized_zero_coefficient]
  rfl

/-- Independent source prices pay the outer spatial numerator cancellation.
Neither a factor witness nor a caller denominator margin enters this producer. -/
theorem source_em_outer_numerator_factor (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) : X^sourceEMOuterOrder event n ∣ sourceEMOuterNumerator event n j := by
  apply bounded_fraction_clock_factor _ _ (2*sourceEMSpatialClockBudget event n 1 j)
    (source_em_outer_denominator_nonzero event n)
  intro eps positive small
  have spatial : eps^2≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ positive.le small 2
  by_cases regular : (sourceEMOuterDenominator event n).eval (eps:ℂ)≠0
  · rw [source_em_outer_fraction_actual event eps n j regular]
    exact source_em_spatial_residue_uniform_price event eps n 1 spatial j
  · have zero : (sourceEMOuterDenominator event n).eval (eps:ℂ)=0 := not_ne_iff.mp regular
    rw [zero,div_zero,norm_zero]
    exact (norm_nonneg (sourceEMClockResidue event 0 n j)).trans
      (source_em_spatial_residue_uniform_price event 0 n 1 (by norm_num) j)

theorem source_em_outer_denominator_coefficient_nonzero (event : DressedEvent)
    (n : PhysicalMomentum) :
    (sourceEMOuterDenominator event n).coeff (sourceEMOuterOrder event n)≠0 :=
  coeff_natTrailingDegree_ne_zero.mpr (source_em_outer_denominator_nonzero event n)

/-- The source spatial factor is directly consumed by its canonical finite
numerator, retaining every original forcing column. -/
theorem source_em_outer_finite_numerator (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    X^sourceEMOuterOrder event n *
      (sourceEMOuterNumerator event n j /ₘ X^sourceEMOuterOrder event n)=
      sourceEMOuterNumerator event n j := by
  obtain ⟨Q,same⟩:=source_em_outer_numerator_factor event n j
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow _)]

private theorem factor_origin (P Q : ℂ[X]) (m : ℕ) (factor : X^m*Q=P) :
    Q.eval 0=P.coeff m := by
  have coefficient : (X^m*Q).coeff m=Q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul Q m 0
  rw [←factor,coefficient]
  exact Q.coeff_zero_eq_eval_zero.symm

/-- The actual finite clock residue now has its own source-generated ordered
spatial return. This does not identify it with exact epsilon-zero or a joint full-field limit. -/
theorem source_em_outer_residue_limit (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    Tendsto (fun eps : ℝ=>sourceEMClockResidue event eps n j) (𝓝[>] 0)
      (𝓝 (sourceEMOuterResidue event n j)) := by
  obtain ⟨Nq,nEq⟩:=source_em_outer_numerator_factor event n j
  have dFactor : X^sourceEMOuterOrder event n ∣ sourceEMOuterDenominator event n :=
    X_pow_dvd_iff.mpr (fun _ low=>coeff_eq_zero_of_lt_natTrailingDegree low)
  obtain ⟨Dq,dEq⟩:=dFactor
  have nValue:=factor_origin _ _ _ nEq.symm
  have dValue:=factor_origin _ _ _ dEq.symm
  have regular : Dq.eval 0≠0 := by
    rw [dValue]
    exact source_em_outer_denominator_coefficient_nonzero event n
  have cn : Continuous (fun eps : ℝ=>Nq.eval (eps:ℂ)) := by fun_prop
  have cd : Continuous (fun eps : ℝ=>Dq.eval (eps:ℂ)) := by fun_prop
  have base:=(cn.continuousAt.div cd.continuousAt regular).tendsto.mono_left
    (show (𝓝[>] (0:ℝ))≤𝓝 0 from inf_le_left)
  simp only [Pi.div_apply,Complex.ofReal_zero] at base
  rw [nValue,dValue] at base
  change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (sourceEMOuterResidue event n j)) at base
  have chart : ∀ᶠeps : ℝ in 𝓝[>] (0:ℝ),
      (sourceEMOuterDenominator event n).eval (eps:ℂ)≠0 :=
    (source_static_punctured_chart _ (source_em_outer_denominator_nonzero event n)).filter_mono
      (nhdsWithin_mono 0 (show Ioi (0:ℝ)⊆({0}ᶜ) from fun eps positive=>by simpa using positive.ne'))
  apply Tendsto.congr' _ base
  filter_upwards [self_mem_nhdsWithin,chart] with eps positive sourceRegular
  rw [←source_em_outer_fraction_actual event eps n j sourceRegular,nEq,dEq,
    eval_mul,eval_mul,eval_pow,eval_X]
  exact (mul_div_mul_left _ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne'))).symm

end LowEnergy.GaussComposite.ActualSourcePreparedEMOuterResidue
