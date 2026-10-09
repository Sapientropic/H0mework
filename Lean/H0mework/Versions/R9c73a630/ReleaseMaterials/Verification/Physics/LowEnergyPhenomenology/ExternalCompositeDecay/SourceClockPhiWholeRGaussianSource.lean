import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeCoframeRSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeJointGaussianSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeComplementGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedFieldGaussian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open SourceClockPhiNormalizedScalarBudget ClockPhiHeatCorrectedCovarianceSource
open FirstCurrentPayer NativePointReturn PositiveClockGenerator MeasureTheory
open scoped InnerProductSpace
private abbrev n : ℝ := sourceTime 0
private abbrev γ := ProbabilityTheory.gaussianReal 0 1
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
attribute [local irreducible] sourcePair embed combinedConjugate diagonalAction correctedCompleteCore
  normalizedState normalizedForcing matchedField matchedTester updatedForcing
  coframeForcing coframeCompleted completeCurrent nativeComplement

def updatedFirstCurrentRemainder (s : ℝ) (hs : 0 < s) (x : ℝ×ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) : ℝ :=
  let w := normalizedState m ell F z hz g
  let u := correctedCompleteCore s hs x.1 x.2 w
  let f := updatedForcing s hs x m ell F z hz g
  2*(sourcePair (A u) (SourceScalarDoubleCurrent.bracket diagonalAction A u)).re+matchedField u+
    (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester u)+((144/n:ℝ):ℂ) • embed f‖^2-
    (n/96)*‖embed (U (D u))‖^2

def firstCurrentGaussianMean (s : ℝ) (hs : 0 < s) (z : ℂ) (w : QuantumTest) : ℝ :=
  (nativePositiveMean s hs w w+localPositiveMean s hs w w).re+matchedFieldMean s hs w+
    (35*n/96)*(clockUDDensity s hs w).re-
    6*(coframeGaussianPair s (matchedGaussianColumn s hs w) (coframeForcingColumn s hs z w)).re-
    (n/48)*(coframeGaussianPair s (matchedGaussianColumn s hs w) (matchedGaussianColumn s hs w)).re

/-- The full original first-current responsibility after its actual clock update has a generated
Gaussian mean. All literal fields, the full updated forcing, and both signed coframe legs are retained. -/
theorem actual_whole_R_gaussian_source (s : ℝ) (hs : 0 < s)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    Integrable (fun x : ℝ×ℝ => updatedFirstCurrentRemainder s hs x m ell F z hz g) (γ.prod γ) ∧
    (∫x : ℝ×ℝ,updatedFirstCurrentRemainder s hs x m ell F z hz g ∂γ.prod γ)=
      firstCurrentGaussianMean s hs z (normalizedState m ell F z hz g) := by
  let w := normalizedState m ell F z hz g
  let q := fun x : ℝ×ℝ => sourcePair (correctedCompleteCore s hs x.1 x.2 w)
    (completeCurrent nativeComplement (correctedCompleteCore s hs x.1 x.2 w))
  let field := fun x : ℝ×ℝ => matchedField (correctedCompleteCore s hs x.1 x.2 w)
  let cp := fun x : ℝ×ℝ => (432/n)*‖embed (coframeForcing s hs x z w)‖^2-
    (n/48)*‖embed (coframeCompleted s hs x z w)‖^2
  let debit := (35*n/96)*(clockUDDensity s hs w).re
  have hN := actual_corrected_native_joint_gaussian s hs w w
  have hF := actual_corrected_matched_field_gaussian s hs w
  have hC := actual_normalized_signed_coframe_gaussian s hs m ell F z hz g
  have hiN : Integrable (fun x => (q x).re) (γ.prod γ) := by
    simpa only [q,RCLike.re_eq_complex_re] using hN.1.re
  have hiF : Integrable field (γ.prod γ) := hF.1
  have hiC : Integrable cp (γ.prod γ) := hC.1
  have hiD : Integrable (fun _ : ℝ×ℝ => debit) (γ.prod γ) := integrable_const _
  have hD (x : ℝ×ℝ) : ‖embed (U (D (correctedCompleteCore s hs x.1 x.2 w)))‖^2=
      (clockUDDensity s hs w).re := by
    rw [actual_corrected_UD_clock_density s hs x.1 x.2 w,←Complex.ofReal_pow,Complex.ofReal_re]
  have he (x : ℝ×ℝ) : updatedFirstCurrentRemainder s hs x m ell F z hz g=
      (q x).re+field x+debit+cp x := by
    have h := actual_corrected_R_coframe_source s hs x m ell F z hz g
    dsimp only at h
    change updatedFirstCurrentRemainder s hs x m ell F z hz g=
      (q x).re+field x+(35*n/96)*‖embed (U (D (correctedCompleteCore s hs x.1 x.2 w)))‖^2+
        (432/n)*‖embed (coframeForcing s hs x z w)‖^2-
        (n/48)*‖embed (coframeCompleted s hs x z w)‖^2 at h
    rw [h,hD]
    dsimp only [debit,cp]
    ring
  have hi := ((hiN.add hiF).add hiD).add hiC
  refine ⟨hi.congr (Filter.Eventually.of_forall fun x => (he x).symm),?_⟩
  simp_rw [he]
  erw [integral_add ((hiN.add hiF).add hiD) hiC,
    integral_add (hiN.add hiF) hiD,integral_add hiN hiF]
  have hnr := Complex.reCLM.integral_comp_comm hN.1
  change (∫x : ℝ×ℝ,(q x).re ∂γ.prod γ)=(∫x : ℝ×ℝ,q x ∂γ.prod γ).re at hnr
  rw [hnr]
  change ((∫x : ℝ×ℝ,q x ∂γ.prod γ).re+(∫x : ℝ×ℝ,field x ∂γ.prod γ))+
    (∫_x : ℝ×ℝ,debit ∂γ.prod γ)+(∫x : ℝ×ℝ,cp x ∂γ.prod γ)=_
  change Integrable q (γ.prod γ) ∧ (∫x : ℝ×ℝ,q x ∂γ.prod γ)=_ at hN
  change Integrable field (γ.prod γ) ∧ (∫x : ℝ×ℝ,field x ∂γ.prod γ)=_ at hF
  change Integrable cp (γ.prod γ) ∧ (∫x : ℝ×ℝ,cp x ∂γ.prod γ)=_ at hC
  rw [hN.2,hF.2,hC.2]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  dsimp only [firstCurrentGaussianMean,debit,w]
  ring
end LowEnergy.FirstCurrentPayerNext
