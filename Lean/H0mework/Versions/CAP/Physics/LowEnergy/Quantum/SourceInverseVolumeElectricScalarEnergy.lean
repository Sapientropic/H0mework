import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricCurrentFactor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricScalarEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceInverseElectricCurrentForm SourceInverseElectricCurrentCoefficient SourceInverseElectricCurrentFactor
open SourceInverseElectricCurrentEnergy SourceScalarDoubleCurrent SourceMixedNativeReturn
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceInverseDefectCurrentResponse
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal ContDiff
attribute [local irreducible] windowCurrent current currentKernel state sourceRead
  SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion

def scalarCurrentLeg (sharp : Bool) (m ell : ℕ) (p : QuantumTest) (r : Row) : QuantumTest :=
  envelopeAction sharp (gaugeDirection r.2.1 r.1) (SourceMixedNativeReturn.thetaAction m ell p)

def weightedScalarCurrentLeg (sharp : Bool) (m ell : ℕ) (q : QuantumTest) (r : Row) : QuantumTest :=
  envelopeAction sharp (gaugeDirection r.2.2 r.1) (SourceMixedNativeReturn.thetaAction m ell
    (multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2) q))

/-- The original current leg is controlled by the same real source-envelope moment. -/
theorem actual_current_leg_energy (sharp : Bool) (m ell : ℕ) (p : QuantumTest) (r : Row) :
    ‖embed (currentLeg sharp m ell p r)‖^2 ≤ ‖embed (scalarCurrentLeg sharp m ell p r)‖^2 := by
  have h := actual_current_energy sharp m ell (gaugeDirection r.2.1 r.1) rfl p
  rw [original_window_current sharp m ell _ rfl] at h
  exact h

private theorem current_multiplier (sharp : Bool) (m ell : ℕ) (v : GaussLiveMomentum.Ambient) (hv : v.1=0)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (q : QuantumTest) :
    multiply c hc (windowCurrent sharp m ell v q)=windowCurrent sharp m ell v (multiply c hc q) := by
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • windowCurrent sharp m ell v q z=_
  rw [original_window_current_apply sharp m ell v hv,original_window_current_apply sharp m ell v hv]
  change (c z : ℂ) • ((SourceNativeCutoffContact.theta m ell z : ℂ) • currentKernel sharp v z (q z))=
    (SourceNativeCutoffContact.theta m ell z : ℂ) • currentKernel sharp v z ((c z : ℂ) • q z)
  rw [map_smul,smul_comm]

/-- Gauge metric weights remain on the input of the same bounded source factor. -/
theorem actual_weighted_current_leg_energy (sharp : Bool) (m ell : ℕ) (q : QuantumTest) (r : Row) :
    ‖embed (weightedCurrentLeg sharp m ell q r)‖^2 ≤
      ‖embed (weightedScalarCurrentLeg sharp m ell q r)‖^2 := by
  have he : weightedCurrentLeg sharp m ell q r=windowCurrent sharp m ell (gaugeDirection r.2.2 r.1)
      (multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2) q) := by
    unfold weightedCurrentLeg
    change multiply (fun z => gaugeWeight z r.2.1 r.2.2) (gaugeWeight_smooth r.2.1 r.2.2)
      ((SourceMixedNativeReturn.thetaAction m ell*current sharp (gaugeDirection r.2.2 r.1)) q)=_
    rw [←original_window_current sharp m ell (gaugeDirection r.2.2 r.1) rfl]
    exact current_multiplier sharp m ell _ rfl _ _ q
  rw [he]
  exact actual_current_energy sharp m ell _ rfl _

/-- Both local CAR-current energies have been replaced by generated scalar weighted moments. -/
def scalarFormBudget (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) : ℝ :=
  (1/2 : ℝ)*((∑ r : Row,‖embed (momentumLeg p r)‖^2)*
      (∑ r : Row,‖embed (weightedScalarCurrentLeg sharp m ell q r)‖^2)+
    (∑ r : Row,‖embed (scalarCurrentLeg (!sharp) m ell p r)‖^2)*
      (∑ r : Row,‖embed (weightedMomentumLeg q r)‖^2))

theorem original_electric_scalar_energy (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    ‖GaussFockPair.sourcePair p (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) q)‖^2 ≤
      scalarFormBudget sharp m ell p q := by
  apply (original_electric_energy sharp m ell p q).trans
  change (1/2 : ℝ)*((∑ r : Row,‖embed (momentumLeg p r)‖^2)*
      (∑ r : Row,‖embed (weightedCurrentLeg sharp m ell q r)‖^2)+
    (∑ r : Row,‖embed (currentLeg (!sharp) m ell p r)‖^2)*
      (∑ r : Row,‖embed (weightedMomentumLeg q r)‖^2)) ≤ _
  unfold scalarFormBudget
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun r _ => actual_weighted_current_leg_energy sharp m ell q r)
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun r _ => actual_current_leg_energy (!sharp) m ell p r)

def scalarResponseBudget (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℝ :=
  scalarFormBudget sharp m ell
    (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (state F z hz g)

/-- The complete sourceRead response now consumes scalar moments of the actual two retarded legs. -/
theorem actual_electric_scalar_response (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z) (g : H))‖^2 ≤
      scalarResponseBudget sharp m ell F z hz g k := by
  rw [actual_read_pair F z hz]
  exact original_electric_scalar_energy sharp m ell _ _

theorem actual_electric_scalar_full_frequency (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (k : H) ((finiteResolvent F (line μ w)*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F (line μ w)) (g : H))‖^2)) ≤
      ∫⁻ w : ℝ,ENNReal.ofReal (scalarResponseBudget sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k) := by
  apply lintegral_mono
  intro w
  exact ENNReal.ofReal_le_ofReal (actual_electric_scalar_response sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k)

end LowEnergy.SourceInverseElectricScalarEnergy
