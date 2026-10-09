import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeCausalScalarPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarCausalFrequencyMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceScalarEssentialBudget SourceScalarDoubleCurrent SourceScalarShiftedBulk
open SourceScalarPositiveBulkWard SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ClockPhiHeatCorrectedCovarianceSource
open SourceJointResidualEnergy SourceFourPoleEnergyClosed MeasureTheory Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] sourcePair embed scalarBulkComplete wholeClockState wholeResponseDerivative
variable {ι : Type*} [Fintype ι]

def wholeNoetherCausalPrice (s : ℝ) (hs : 0 < s) (half advanced : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (x : ℝ×ℝ) (q : ℝ) : ℝ :=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)-
    2*(sourcePair (wholeReverseSource s hs half advanced m ell F g x q)
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))).re

/-- The complete original finite Noether work consumes the source-generated
causal sign. Its remaining price is the actual energy and full source word. -/
theorem actual_whole_noether_causal_price (s : ℝ) (hs : 0 < s) (half advanced : Bool)
    (m ell : ℕ) (F : Index) (g : diagonal.domain) (x : ℝ×ℝ) (h : ℝ) (hh : 0 < h) :
    let W := fun q : ℝ => let z := actualFrequency advanced (sourceNoetherFrequency half) q
      let a := clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
      reverseScalarNoetherWork h z a.1 a.2
    Integrable W ∧ Integrable (wholeNoetherCausalPrice s hs half advanced m ell F g x) ∧
      (∫ q : ℝ, W q) ≤ ∫ q : ℝ, wholeNoetherCausalPrice s hs half advanced m ell F g x q := by
  dsimp only
  let C := fun q : ℝ => (actualFrequency advanced (sourceNoetherFrequency half) q).im*
    (sourcePair (wholeResponseDerivative s hs half advanced m ell F g x q)
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))).im
  let P := wholeNoetherCausalPrice s hs half advanced m ell F g x
  let J := wholeScalarFrequencyRemainder s hs half advanced m ell F g x
  have hw := actual_whole_reverse_scalar_frequency_integral s hs half advanced m ell F g x h hh
  have hc := actual_whole_scalar_causal_cross_payment s hs half advanced m ell F g x
  have hcint : Integrable C := by
    have hi : Integrable (fun q : ℝ => (sourcePair (wholeResponseDerivative s hs half advanced m ell F g x q)
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))).im) := hc.1.im
    have hμ (q : ℝ) : (actualFrequency advanced (sourceNoetherFrequency half) q).im =
        causalDirection advanced*sourceNoetherFrequency half := by
      cases advanced <;> simp [actualFrequency, causalDirection, line_im]
    simpa only [C, hμ] using hi.const_mul (causalDirection advanced*sourceNoetherFrequency half)
  have hj : J = P + (36 : ℝ) • C := by
    funext q
    dsimp only [J, P, wholeScalarFrequencyRemainder, wholeNoetherCausalPrice, C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hp : Integrable P := by
    have hi := hw.2.1.sub (hcint.const_mul 36)
    exact hi.congr (Eventually.of_forall (fun q => by
      change J q-36*C q=P q
      rw [hj]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right]))
  refine ⟨hw.1, hp, ?_⟩
  rw [hw.2.2]
  change (∫ q : ℝ, J q) ≤ ∫ q : ℝ, P q
  rw [hj]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add hp (hcint.const_mul 36)]
  change (∫ q : ℝ, P q)+(∫ q : ℝ, 36*C q) ≤ _
  rw [integral_const_mul]
  have hsign : (∫ q : ℝ, C q) ≤ 0 := hc.2
  linarith only [hsign]
end LowEnergy.ScalarCausalFrequencyMoment
