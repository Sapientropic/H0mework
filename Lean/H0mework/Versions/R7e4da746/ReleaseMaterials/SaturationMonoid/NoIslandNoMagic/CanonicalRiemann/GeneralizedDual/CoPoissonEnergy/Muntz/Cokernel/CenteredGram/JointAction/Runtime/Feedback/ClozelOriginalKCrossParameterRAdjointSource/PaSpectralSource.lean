import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Source.Jet

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaSpectralSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
local notation "K" => burnolCompletedMellinRieszVector
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local instance spectralPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem compact_source_coefficient (c : BurnolCompletedMellinCoordinate) (source : burnolCompactAnnulusSource) :
    burnolPaResolventSourceCoefficient c (burnolCompactAdditivePhysicalState source)=
      coPoissonMuntzEvenSourceMellin source.1 (1-c.value) := by
  rw [burnolPaResolventSourceCoefficient_compact]
  unfold burnolFirstSourceMellinCoefficient
  ring

/-- All Gamma and factor-two normalization is consumed from the original Fourier/co-Poisson source identity. -/
theorem compact_fourier_source_read (c : BurnolCompletedMellinCoordinate) (source : burnolCompactAnnulusSource) :
    inner ℂ (F (K c)) (burnolCompactAdditivePhysicalState source)=
      (riemannZeta c.value/2)*burnolPaResolventSourceCoefficient c (burnolCompactAdditivePhysicalState source) := by
  have cPositive : 0<c.value.re := by linarith [c.rightHalf]
  have compPositive : 0<(1-c.value).re := by simp only [sub_re,one_re];linarith [c.belowOne]
  have compBelow : (1-c.value).re<1 := by simp only [sub_re,one_re];linarith [c.rightHalf]
  have cNe : c.value≠0 := ne_of_apply_ne Complex.re (by simpa only [Complex.zero_re] using cPositive.ne')
  have compNe : 1-c.value≠0 := ne_of_apply_ne Complex.re (by simpa only [Complex.zero_re] using compPositive.ne')
  have gammaNe := Gammaℝ_ne_zero_of_re_pos cPositive
  have compGammaNe := Gammaℝ_ne_zero_of_re_pos compPositive
  have gammaFactor : Gammaℝ c.value*riemannZeta c.value=
      Gammaℝ (1-c.value)*riemannZeta (1-c.value) := by
    rw [riemannZeta_def_of_ne_zero cNe,riemannZeta_def_of_ne_zero compNe,
      mul_div_cancel₀ _ gammaNe,mul_div_cancel₀ _ compGammaNe,completedRiemannZeta_one_sub]
  have factor := coPoissonMuntzScaleRemainder_mellin_factorization source.1 compPositive compBelow
  have read := two_mul_burnolCompactAdditiveMellinRead_eq_mellin source (1-c.value)
  rw [factor,←compact_source_coefficient c source] at read
  have sourceSquare := burnolCompactAdditiveFourierHomogeneousIdentity source c
  have innerSquare := (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map (K c) (F (burnolCompactAdditivePhysicalState source))
  have invol : F (F (burnolCompactAdditivePhysicalState source))=burnolCompactAdditivePhysicalState source :=
    evenFaceFourier_involutive burnolUnscaledCommonGapRadius _
  rw [invol] at innerSquare
  rw [innerSquare,burnolCompletedMellinRieszVector_readback]
  apply mul_left_cancel₀ gammaNe
  calc
    Gammaℝ c.value*burnolCompletedMellinEvaluator c (F (burnolCompactAdditivePhysicalState source))=
      Gammaℝ (1-c.value)*burnolCompactAdditiveMellinRead source (1-c.value) := sourceSquare
    _ = (Gammaℝ (1-c.value)*riemannZeta (1-c.value))*
        (burnolPaResolventSourceCoefficient c (burnolCompactAdditivePhysicalState source)/2) := by
      linear_combination (Gammaℝ (1-c.value)/2)*read
    _ = Gammaℝ c.value*((riemannZeta c.value/2)*
        burnolPaResolventSourceCoefficient c (burnolCompactAdditivePhysicalState source)) := by rw [←gammaFactor];ring

/-- The complete Fourier-stable Pa closure is consumed, not a caller-supplied faithful-source witness. -/
theorem allPa_fourier_source_read (c : BurnolCompletedMellinCoordinate)
    (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (F (K c)) g=(riemannZeta c.value/2)*burnolPaResolventSourceCoefficient c g := by
  let defect : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
    innerSL ℂ (F (K c))-(riemannZeta c.value/2) • burnolPaResolventSourceCoefficient c
  have compact (source : burnolCompactAnnulusSource) : defect (burnolCompactAdditivePhysicalState source)=0 := by
    change inner ℂ (F (K c)) _-(riemannZeta c.value/2)*burnolPaResolventSourceCoefficient c _=0
    rw [compact_fourier_source_read,sub_self]
  have generator (index : BurnolCompactCoPoissonGeneratorIndex) : defect (burnolCompactCoPoissonGenerator index)=0 := by
    rcases index with ⟨source,parity⟩
    fin_cases parity
    · exact compact source
    · have same : burnolCompactCoPoissonGenerator (source,(1:Fin 2))=
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change defect (burnolCompactCoPoissonGenerator (source,(1:Fin 2)))=0
      rw [same]
      exact compact _
  have sourceIn (input : BurnolCompactCoPoissonLinearSource) : defect (burnolCompactCoPoissonLanding input)=0 := by
    induction input using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add,map_add,ha,hb,add_zero]
    | single index coefficient => rw [burnolCompactCoPoissonLanding_single,map_smul,generator,smul_zero]
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ defect.ker := by
    rintro _ ⟨input,rfl⟩
    exact sourceIn input
  have killed := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe defect.isClosed_ker inside
  change inner ℂ (F (K c)) g-(riemannZeta c.value/2)*burnolPaResolventSourceCoefficient c g=0 at killed
  exact sub_eq_zero.mp killed

/-- Full Pa projection of the original Fourier K family, at its true source parameter. -/
theorem FourierK_Pa_source_family (c : BurnolCompletedMellinCoordinate) :
    OriginalKCombCofinalPaAction.E (fourierL2 (K c : BurnolL2))=
      star (riemannZeta c.value/2) • paCoefficientSource c := by
  let field := star (riemannZeta c.value/2) • paCoefficientSource c
  have belongs : field∈burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
      (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
        (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
          (OriginalPrimitiveRankBalance.conjugateCoordinate c)).property)
  have normal (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
      inner ℂ g (OriginalKCombCofinalPaAction.E (fourierL2 (K c : BurnolL2)))=inner ℂ g field := by
    rw [OriginalKCombCofinalPaAction.wholePa_normal_read _ g inside]
    have read := congrArg star (allPa_fourier_source_read c g inside)
    simp only [star_mul,star_div₀,star_ofNat] at read
    have readHerm : star (inner ℂ (F (K c)) g)=inner ℂ g (F (K c)) := inner_conj_symm (𝕜:=ℂ) g (F (K c))
    rw [readHerm] at read
    change inner ℂ (g : BurnolL2) (fourierL2 (K c : BurnolL2))=
      inner ℂ g (star (riemannZeta c.value/2) • paCoefficientSource c)
    rw [inner_smul_right]
    have covector := congrArg star (paCoefficientSource_read c g inside)
    have covectorHerm : star (inner ℂ (paCoefficientSource c) g)=inner ℂ g (paCoefficientSource c) :=
      inner_conj_symm (𝕜:=ℂ) g (paCoefficientSource c)
    rw [covectorHerm] at covector
    change inner ℂ g (F (K c))=_
    rw [covector]
    simpa only [star_div₀,star_ofNat,mul_comm] using read
  have diffIn : OriginalKCombCofinalPaAction.E (fourierL2 (K c : BurnolL2))-field∈burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem
      (Submodule.starProjection_apply_mem _ (burnolEvenAmbientProjection (fourierL2 (K c : BurnolL2)))) belongs
  have zero : inner ℂ (OriginalKCombCofinalPaAction.E (fourierL2 (K c : BurnolL2))-field)
      (OriginalKCombCofinalPaAction.E (fourierL2 (K c : BurnolL2))-field)=0 := by
    rw [inner_sub_right,normal _ diffIn,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

end OriginalKCrossParameterRAdjointSource.PaSpectralSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
