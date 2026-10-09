import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedInputFullSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiAffineInputHardyWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeRadialInputPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarInputJointNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockPhiNativeJointPayment
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer
open PrimitiveInputPayer ClockPhiHeatCorrectedCovarianceSource SourceClockPhiRadiusSourceCurrent
open MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev B:End:=scalarBulkComplete
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction completeBalancedInput balancedInputVector
  correctedCompleteCore wholeSourceMap wholeSourceNext wholeClockState radialInputUpper inputScalarWardPrice
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_gap(half:Bool):2*n<sourceNoetherFrequency half:=by
  have h:=actual_source_noether_gap half
  linarith [n_pos]
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by linarith [n_pos,frequency_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q

def wholeInputWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):End:=
  correctedCompleteCore s hs x.1 x.2*wholeSourceMap s hs half advanced m ell F g

def wholeInputForcing(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  balancedInputForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g
    (wholeInputWord s hs half advanced m ell F g x)
private theorem whole_input_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeInputWord s hs half advanced m ell F g x
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)=
        completeBalancedInput s hs half advanced m ell F g x q:=by
  unfold wholeInputWord completeBalancedInput
  rfl

/-- The actual input entering the physical price carries the same four-column forcing, including every own-delta and clock/electric outer commutator. -/
theorem actual_whole_input_full_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    diagonalAction (completeBalancedInput s hs half advanced m ell F g x q)=
      wholeInputForcing s hs half advanced m ell F g x q+
        actualFrequency advanced (sourceNoetherFrequency half) q • completeBalancedInput s hs half advanced m ell F g x q:=by
  have h:=actual_balanced_input_full_source m ell F _ (hz half advanced q) g (wholeInputWord s hs half advanced m ell F g x)
  simpa only [whole_input_return,wholeInputForcing] using h

def wholeInputScalarWard(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  inputScalarWardPrice advanced (completeBalancedInput s hs half advanced m ell F g x q)
    (wholeInputForcing s hs half advanced m ell F g x q)

theorem actual_whole_input_scalar_gap(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (sourceNoetherFrequency half-2*n)*scalarEnergy (completeBalancedInput s hs half advanced m ell F g x q) ≤
      wholeInputScalarWard s hs half advanced m ell F g x q ∧
    ‖embed (S (U (completeBalancedInput s hs half advanced m ell F g x q)))‖^2 ≤
      (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*wholeInputScalarWard s hs half advanced m ell F g x q:=by
  exact actual_full_source_input_scalar_gap _ (frequency_gap half) advanced q _ _
    (actual_whole_input_full_source s hs half advanced m ell F g x q)
private theorem whole_input_word_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (completeBalancedInput s hs half advanced m ell F g x q))‖^2):=by
  have h:=actual_balanced_input_word_integrable _ (frequency_positive half) advanced m ell F g
    (L*wholeInputWord s hs half advanced m ell F g x)
  simpa only [Module.End.mul_apply,whole_input_return] using h

/-- The complete input Ward is an ordinary full-frequency L1 word. Its actual four-column zero law removes the apparent constant forcing tail. -/
theorem actual_whole_input_scalar_ward_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (wholeInputScalarWard s hs half advanced m ell F g x):=by
  let T:=wholeInputWord s hs half advanced m ell F g x
  have hf:Integrable (fun q:ℝ=>(sourcePair (wholeInputForcing s hs half advanced m ell F g x q)
      (B (completeBalancedInput s hs half advanced m ell F g x q))).im):=by
    have h:=(actual_balanced_input_forcing_pair_integrable _ (frequency_positive half) advanced m ell F g T 1 (B*T)).im
    simpa only [T,Module.End.one_apply,Module.End.mul_apply,whole_input_return,wholeInputForcing,RCLike.im_eq_complex_im] using h
  have hg:Integrable (fun q:ℝ=>(sourcePair (completeBalancedInput s hs half advanced m ell F g x q)
      (geometricScalarCurrent (completeBalancedInput s hs half advanced m ell F g x q))).im):=by
    have h:=(actual_balanced_input_pair_integrable _ (frequency_positive half) advanced m ell F g T (geometricScalarCurrent*T)).im
    simpa only [T,Module.End.mul_apply,whole_input_return,RCLike.im_eq_complex_im] using h
  have hn:=whole_input_word_integrable s hs half advanced m ell F g x 1
  simp only [Module.End.one_apply] at hn
  unfold wholeInputScalarWard inputScalarWardPrice
  exact (((hf.sub (hg.div_const 2)).const_mul (inputCausalSign advanced)).add
    (hn.const_mul (n^2*‖vacuum‖^2)))

def jointInputScalarUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  radialInputUpper s hs half advanced m ell F g x q+
    (56*n*(reverseNoetherFactor half)^2/3)*
      ((4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*wholeInputScalarWard s hs half advanced m ell F g x q-
        ‖embed (S (U (completeBalancedInput s hs half advanced m ell F g x q)))‖^2)
private theorem joint_upper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    radialInputUpper s hs half advanced m ell F g x q ≤ jointInputScalarUpper s hs half advanced m ell F g x q:=by
  have h:=(actual_whole_input_scalar_gap s hs half advanced m ell F g x q).2
  have hC:0 ≤ 56*n*(reverseNoetherFactor half)^2/3:=by have hn:=n_pos;positivity
  unfold jointInputScalarUpper
  exact le_add_of_nonneg_right (mul_nonneg hC (sub_nonneg.mpr h))

/-- The original physical J and its generated scalar/vacuum loss now consume the source-native input Ward. The original own-QF/local/matter terms remain in the same radial upper; no independent U graph or scalar-energy budget is assumed. -/
theorem actual_whole_joint_input_scalar_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (fun q:ℝ=>scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    Integrable (jointInputScalarUpper s hs half advanced m ell F g x) ∧
    0 ≤ (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ≤
        ∫q:ℝ,jointInputScalarUpper s hs half advanced m ell F g x q:=by
  have h:=actual_whole_radial_input_payment s hs half advanced m ell F g x
  have hw:=actual_whole_input_scalar_ward_integrable s hs half advanced m ell F g x
  have hn:=whole_input_word_integrable s hs half advanced m ell F g x (S*U)
  simp only [Module.End.mul_apply] at hn
  have hu:Integrable (jointInputScalarUpper s hs half advanced m ell F g x):=
    h.2.2.1.add (((hw.const_mul (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))).sub hn).const_mul
      (56*n*(reverseNoetherFactor half)^2/3))
  exact ⟨h.1,h.2.1,hu,h.2.2.2.1,h.2.2.2.2.trans
    (integral_mono h.2.2.1 hu (joint_upper s hs half advanced m ell F g x))⟩

def baseInputScalarWard(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):ℝ:=
  inputScalarWardPrice advanced
    (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)
    (balancedInputForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g 1)

/-- The base input of the amplitude/cofinal consumer has a generated native Ward price. The full source, own projection and covariant spatial current remain joined; no independent weighted response tail is assumed. -/
theorem actual_base_input_scalar_ward_payment(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (baseInputScalarWard half advanced m ell F g) ∧
    (∫q:ℝ,‖embed (S (U (balancedInputVector m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)))‖^2) ≤
      (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*
        (∫q:ℝ,baseInputScalarWard half advanced m ell F g q):=by
  have hf:Integrable (fun q:ℝ=>(sourcePair
      (balancedInputForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g 1)
      (B (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))).im):=by
    simpa only [Module.End.one_apply,RCLike.im_eq_complex_im] using
      (actual_balanced_input_forcing_pair_integrable _ (frequency_positive half) advanced m ell F g 1 1 B).im
  have hg:Integrable (fun q:ℝ=>(sourcePair
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)
      (geometricScalarCurrent (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))).im):=by
    simpa only [Module.End.one_apply,RCLike.im_eq_complex_im] using
      (actual_balanced_input_pair_integrable _ (frequency_positive half) advanced m ell F g 1 geometricScalarCurrent).im
  have hn:=actual_balanced_input_word_integrable _ (frequency_positive half) advanced m ell F g 1
  simp only [Module.End.one_apply] at hn
  have hi:Integrable (baseInputScalarWard half advanced m ell F g):=by
    unfold baseInputScalarWard inputScalarWardPrice
    exact (((hf.sub (hg.div_const 2)).const_mul (inputCausalSign advanced)).add
      (hn.const_mul (n^2*‖vacuum‖^2)))
  refine ⟨hi,?_⟩
  have hl:=actual_balanced_input_word_integrable _ (frequency_positive half) advanced m ell F g (S*U)
  simp only [Module.End.mul_apply] at hl
  have hp(q:ℝ):‖embed (S (U (balancedInputVector m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)))‖^2 ≤
      (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*baseInputScalarWard half advanced m ell F g q:=by
    have he:=actual_balanced_input_full_source m ell F _ (hz half advanced q) g 1
    simp only [Module.End.one_apply] at he
    exact (actual_full_source_input_scalar_gap _ (frequency_gap half) advanced q _ _ he).2
  have h:=integral_mono hl (hi.const_mul _) hp
  rw [integral_const_mul] at h
  exact h
end LowEnergy.ScalarInputJointNoether
