import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherCommon
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarVirialBulk SourceScalarInverseNativeEnergy
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open SourceClockPhiNormalizedScalarBudget SourceClockPhiOriginalGaussianH0FirstJet SourceCoframeCovariantAction
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockReflectedForm
open FirstCurrentPayerNext FinitePhysicalSource NativePointReturn MeasureTheory Filter
open scoped InnerProductSpace ENNReal
private abbrev n : ℝ := sourceTime 0
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
attribute [local irreducible] sourcePair embed normalizedState matchedTester covariantKinetic
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]

def remainingNativeField (w : QuantumTest) : ℝ :=
  ((22:ℂ)*sourcePair w (U (gaugeKinetic w))+
    (12:ℂ)*sourcePair w (U (scalarSpatialAction w))+
    (16:ℂ)*sourcePair w (U (magneticAction w))+localPairJet w w).re+
    12*n*spinForm (U w)+12*n*densityForm (U w)-12*gaugeForm (U w)-12*spatialForm (U w)

/-- This is the complete native/local Q(N) plus the literal field; the matter term cancels internally. -/
theorem actual_native_field_scalar_split (w : QuantumTest) :
    (sourcePair w (completeCurrent nativeComplement w)).re+matchedField w=
      scalarNativePrice w+remainingNativeField w := by
  rw [actual_native_complement_Q_jet]
  unfold nativePairJet matchedField scalarNativePrice scalarNativeBlock remainingNativeField
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.re_ofNat,Complex.im_ofNat,Complex.neg_re,Complex.neg_im,
    Complex.div_re,Complex.div_im,Complex.normSq_ofNat,mul_zero,zero_mul,sub_zero,neg_zero]
  norm_num
  ring

def scalarAbsorbedRemainder (w : QuantumTest) (z : ℂ) : ℝ :=
  remainingNativeField w+(35*n/96)*‖embed (U (D w))‖^2+
    (432/n)*‖embed (covariantKinetic w-z • w)‖^2-
    (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed (covariantKinetic w-z • w)‖^2-
    13*n*inverseNativeEnergy w-6*n*scalarPaymentSquare w
private theorem frequency_pos (half : Bool) : 0<sourceNoetherFrequency half := by
  have hn:0<n:=by
    change 0<sourceTime 0
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private theorem frequency_nonreal (half advanced : Bool) (x : ℝ) :
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using (frequency_pos half).ne'

def originalScalarAbsorptionGap (half advanced : Bool) (m ell : ℕ) (F : Index) (x : ℝ)
    (g : diagonal.domain) : ℝ :=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  firstCurrentJointRemainder m ell F z hz g-
    (scalarNoetherFactor half*scalarPrice m ell F z hz g advanced+scalarAbsorbedRemainder w z)
private theorem absorption_return (half advanced : Bool) (m ell : ℕ) (F : Index) (x : ℝ)
    (g : diagonal.domain) :
    originalScalarAbsorptionGap half advanced m ell F x g=scalarNoetherGap half advanced m ell F x g := by
  unfold originalScalarAbsorptionGap scalarNoetherGap
  dsimp only
  rw [actual_original_R_coframe_source,actual_native_field_scalar_split]
  unfold scalarAbsorbedRemainder
  ring

/-- The same actual R now consumes a strict fraction of its original full-forcing scalar Noether word.
All coframe signs remain, together with two generated negative scalar square groups. -/
theorem actual_original_R_scalar_noether_payment (half : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index), ∀ advanced : Bool,
      (∫⁻x:ℝ,ENNReal.ofReal (originalScalarAbsorptionGap half advanced m ell F x g))≤ENNReal.ofReal ε := by
  simpa only [absorption_return] using actual_scalar_noether_common_payment half g
end LowEnergy.FirstCurrentJointBudget
