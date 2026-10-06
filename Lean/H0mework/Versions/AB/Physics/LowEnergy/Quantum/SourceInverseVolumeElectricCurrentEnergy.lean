import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricCurrentCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricCurrentEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumScalarChart
open SourceInverseElectricCurrentForm SourceInverseElectricCurrentCoefficient SourceScalarDoubleCurrent
open SourceMixedNativeReturn SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceInverseDefectCurrentResponse
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
abbrev Row := LieIndex × Fin 3 × Fin 3
attribute [local irreducible] current sourcePair state sourceRead
  SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion

def momentumLeg (p : QuantumTest) (r : Row) : QuantumTest :=
  covariantMomentum (gaugeDirection r.2.1 r.1) p

def currentLeg (sharp : Bool) (m ell : ℕ) (p : QuantumTest) (r : Row) : QuantumTest :=
  SourceMixedNativeReturn.thetaAction m ell (current sharp (gaugeDirection r.2.1 r.1) p)

def weightedMomentumLeg (q : QuantumTest) (r : Row) : QuantumTest :=
  multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2)
    (covariantMomentum (gaugeDirection r.2.2 r.1) q)

def weightedCurrentLeg (sharp : Bool) (m ell : ℕ) (q : QuantumTest) (r : Row) : QuantumTest :=
  multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2)
    (SourceMixedNativeReturn.thetaAction m ell (current sharp (gaugeDirection r.2.2 r.1) q))

private def legEnergy (v : Row → QuantumTest) : ℝ := ∑ r,‖embed (v r)‖^2

/-- Each product retains a windowed current factor; kinetic-kinetic cross costs are not introduced. -/
def formBudget (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) : ℝ :=
  (1/2 : ℝ)*(legEnergy (momentumLeg p)*legEnergy (weightedCurrentLeg sharp m ell q)+
    legEnergy (currentLeg (!sharp) m ell p)*legEnergy (weightedMomentumLeg q))

private theorem sum_pair_bound (p q : Row → QuantumTest) :
    ‖∑ r,sourcePair (p r) (q r)‖^2 ≤ legEnergy p*legEnergy q := by
  have hp : ‖∑ r,sourcePair (p r) (q r)‖ ≤ ∑ r,‖embed (p r)‖*‖embed (q r)‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    unfold sourcePair
    exact norm_inner_le_norm (embed (p r)) (embed (q r))
  exact (pow_le_pow_left₀ (norm_nonneg _) hp 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => ‖embed (p r)‖) (fun r => ‖embed (q r)‖))

private theorem half_add_bound (a b : ℂ) : ‖(1/2 : ℂ)*(a+b)‖^2 ≤ (1/2 : ℝ)*(‖a‖^2+‖b‖^2) := by
  have h := norm_add_le a b
  rw [norm_mul,mul_pow]
  norm_num
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]

/-- The complete original electric force is bounded by genuine two-leg source energies. -/
theorem original_electric_energy (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    ‖sourcePair p (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) q)‖^2 ≤
      formBudget sharp m ell p q := by
  have h := original_electric_form sharp m ell p q
  have hs : sourcePair p (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) q)=
      (1/2 : ℂ)*((∑ r : Row,sourcePair (momentumLeg p r) (weightedCurrentLeg sharp m ell q r))+
        ∑ r : Row,sourcePair (currentLeg (!sharp) m ell p r) (weightedMomentumLeg q r)) := by
    simpa only [Fintype.sum_prod_type,Finset.sum_add_distrib,momentumLeg,currentLeg,
      weightedMomentumLeg,weightedCurrentLeg] using h
  rw [hs]
  exact (half_add_bound _ _).trans (mul_le_mul_of_nonneg_left
    (add_le_add (sum_pair_bound _ _) (sum_pair_bound _ _)) (by norm_num))

/-- Both actual source frequencies remain in the energy budget. -/
def responseBudget (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℝ :=
  formBudget sharp m ell
    (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (state F z hz g)

theorem actual_electric_response_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z) (g : H))‖^2 ≤
      responseBudget sharp m ell F z hz g k := by
  rw [actual_read_pair F z hz]
  exact original_electric_energy sharp m ell _ _

/-- The original full-frequency integral consumes the moving energy product, with no reader-norm premise. -/
theorem actual_electric_full_frequency (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (k : H) ((finiteResolvent F (line μ w)*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F (line μ w)) (g : H))‖^2)) ≤
    ∫⁻ w : ℝ,ENNReal.ofReal (responseBudget sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k) := by
  apply lintegral_mono
  intro w
  exact ENNReal.ofReal_le_ofReal (actual_electric_response_energy sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k)

end LowEnergy.SourceInverseElectricCurrentEnergy
