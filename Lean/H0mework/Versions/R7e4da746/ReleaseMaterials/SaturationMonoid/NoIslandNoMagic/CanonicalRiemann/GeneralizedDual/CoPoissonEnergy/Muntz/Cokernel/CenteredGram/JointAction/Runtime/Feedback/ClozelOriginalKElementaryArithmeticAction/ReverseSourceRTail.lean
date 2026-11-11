import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Units
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalReverseSourceRTail
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction OriginalKSourceResolventReconstruction
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalPaPhysicalGreen OriginalKFiniteOrderRelease
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Cut" => originalPhysicalCutoff q
local notation "R" => burnolDirectRightResolventCLM
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Pi" => burnolEvenAmbientProjection
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

open private inward_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

private def gamma (c:BurnolCompletedMellinCoordinate) : ℂ :=
  star c.value*GapEuler.gapMean q c

private theorem conjugate_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    riemannZeta (barC c).value=0 := by
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,Complex.star_def,zero,map_zero] using
    riemannZeta_conj c.value

private theorem gamma_ne_zero (c:BurnolCompletedMellinCoordinate) : gamma c≠0 := by
  have cNe:c.value≠0 := by intro same;have h:=c.rightHalf;rw [same] at h;norm_num at h
  have powerNe:(q:ℂ)^(-star c.value)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have gapNe:GapEuler.gapMean q c≠0 := by
    intro same
    have law:=GapEuler.gapMean_primitive q (by norm_num) c
    rw [same,mul_zero] at law
    exact (mul_ne_zero (by norm_num) powerNe) law.symm
  exact mul_ne_zero (star_ne_zero.mpr cNe) gapNe

private theorem reverse_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    reflectL2 (elementaryReverseSource c zero)=elementaryReverseSource c zero := by
  apply Lp.ext
  have raw:=elementary_reverse_raw c zero
  filter_upwards [Lp.coeFn_compMeasurePreserving (elementaryReverseSource c zero) negMeasurePreserving,
    raw,negMeasurePreserving.quasiMeasurePreserving.ae raw] with x reflected right left
  change reflectL2 (elementaryReverseSource c zero) x=elementaryReverseSource c zero (-x) at reflected
  rw [reflected,left,right]
  simp only [elementaryReverseRaw,DualSourceRaw.channels,abs_neg]

/-- The two actual finite-Dirichlet unit sources generate a complete original R equation. -/
theorem reverse_R_equation (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    ((c.value-star c.value)*gamma (barC c)) • R c (elementaryReverseSource c zero)=
      (2*gamma c) • elementaryReverseSource (barC c) (conjugate_zero c zero)-
      (2*gamma (barC c)) • elementaryReverseSource c zero := by
  have right:1/4<(c.value/2).re := by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have starRight:1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have inverse:=burnolDirectRightResolvent_identity (c.value/2) (star c.value/2)
    right starRight ConstantDual.value
  change R c ConstantDual.value-R (barC c) ConstantDual.value=
    (c.value/2-star c.value/2) • R c (R (barC c) ConstantDual.value) at inverse
  have first:=elementary_reverse_unit_resolvent c zero
  change elementaryReverseSource c zero=gamma c •
    (ConstantDual.value-((1-star c.value)/2) • R (barC c) ConstantDual.value) at first
  have second:=elementary_reverse_unit_resolvent (barC c) (conjugate_zero c zero)
  change elementaryReverseSource (barC c) (conjugate_zero c zero)=gamma (barC c) •
    (ConstantDual.value-((1-star (star c.value))/2) •
      burnolDirectRightResolvent (star (star c.value)/2) ConstantDual.value) at second
  rw [star_star] at second
  change elementaryReverseSource (barC c) (conjugate_zero c zero)=gamma (barC c) •
    (ConstantDual.value-((1-c.value)/2) • R c ConstantDual.value) at second
  have acted:=congrArg (R c) first
  rw [map_smul,map_sub,map_smul] at acted
  linear_combination (norm:=module)
    ((c.value-star c.value)*gamma (barC c)) • acted+
    (gamma c*gamma (barC c)*(1-star c.value)) • inverse-
    (2*gamma c) • second+(2*gamma (barC c)) • first

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "z" => elementaryReverseSource c observation.mathlibZero

private theorem difference_ne_zero : (c).value-star (c).value≠0 := by
  have actual:=OriginalKRealCoordinateSourceUnit.actual_original_source_difference_ne_zero
    observation nontrivial half
  exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp actual))

/-- Compactness follows from the actual two-source equation after its generated noncollision. -/
theorem original_reverse_R_compact : Cut (R c z)=R c z := by
  have actual:=reverse_R_equation c observation.mathlibZero
  have left:=elementary_reverse_support c observation.mathlibZero
  have right:=elementary_reverse_support (barC c) (conjugate_zero c observation.mathlibZero)
  have equation:=congrArg Cut actual
  unfold originalPhysicalCutoff at equation
  rw [map_smul,map_sub,map_smul,map_smul,map_smul,map_sub,map_smul,map_smul] at equation
  change (((c).value-star (c).value)*gamma (barC c)) • Cut (R c z)=
    (2*gamma c) • Cut (elementaryReverseSource (barC c) (conjugate_zero c observation.mathlibZero))-
    (2*gamma (barC c)) • Cut z at equation
  rw [left,right] at equation
  exact (smul_right_injective _ (mul_ne_zero (difference_ne_zero observation nontrivial half)
    (gamma_ne_zero (barC c)))) (equation.trans actual.symm)

private theorem quarter_tail_ne_zero (coordinate:BurnolCompletedMellinCoordinate) :
    burnolRadiusNormalizedUnitTail coordinate q (by norm_num)≠0 := by
  intro assumed
  have action:=burnolRadiusNormalizedUnitTail_dilation coordinate q (by norm_num) (-Real.log 16)
  have actionAtFour : burnolMultiplicativeDilation (-Real.log 16)
      (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=
      fullMellinTranslationCharacter coordinate.value (-Real.log 16) •
        burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num) := by
    simpa only [neg_neg,Real.exp_log (by norm_num : (0:ℝ)<16),
      show (1/4:ℝ)*16=4 by norm_num] using action
  clear action
  have action:=actionAtFour
  rw [assumed,map_zero] at action
  have nonzero:fullMellinTranslationCharacter coordinate.value (-Real.log 16)≠0 := Complex.exp_ne_zero _
  have tail:burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)=burnolNormalizedFirstSourceUnitTail coordinate := rfl
  rw [tail] at action
  exact (smul_ne_zero nonzero (burnolOriginalUnitTail_nonzero coordinate)) action.symm

/-- The actual original-c coefficient is computed from that same compact R action. -/
theorem original_reverse_source_R_tail :
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c z=0 := by
  have actual:=OriginalKCompactAdjointRSource.actual_compact_R_rank_source c z
    (elementary_reverse_support c observation.mathlibZero) (reverse_even c observation.mathlibZero)
  change R c z=Cut (R c z)+
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c z •
      burnolRadiusNormalizedUnitTail c q (by norm_num) at actual
  rw [original_reverse_R_compact observation nontrivial half] at actual
  have paid:OriginalKCompactAdjointRSource.actualCompactTailCoefficient c z •
      burnolRadiusNormalizedUnitTail c q (by norm_num)=0 := by linear_combination (norm:=module) -actual
  exact (smul_eq_zero.mp paid).resolve_right (quarter_tail_ne_zero c)

/-- Both actual B feet consume this same zero-owned complete source; it is not a raw actor. -/
theorem original_reverse_source_R_B :
    burnolAmbientMeanZeroFirstCorrection (R c z)=
      GenericSourceStepBAction.secondNext (barC c) (fourierL2 z) ∧
    burnolAmbientMeanZeroSecondCorrection (R c z)=
      GenericSourceStepBAction.firstNext (barC c) (fourierL2 z) :=
  GenericSourceStepBAction.actual_forward_R_B c z (reverse_even c observation.mathlibZero)


/-- The complete original mean survives the source tail calculation. -/
theorem original_reverse_R_physical :
    Pi (R c z)=(-(FiniteMobiusResolventFlux.actualMean z)/((c).value-1)) • G := by
  have compact:=elementary_reverse_support c observation.mathlibZero
  have even:=reverse_even c observation.mathlibZero
  have generated:=OriginalKCoupledPhysicalRFieldSource.actual_compact_projected_R_source c z compact even
  change Pi (R c z)=OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c z at generated
  apply generated.trans
  unfold OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField
  rw [original_reverse_source_R_tail observation nontrivial half]
  simp only [zero_mul,mul_zero,neg_zero,zero_smul,zero_add,add_zero,zero_sub]
  have ne:(c).value-1≠0 := by
    apply sub_ne_zero.mpr
    intro same
    have bound:=(c).belowOne
    rw [same] at bound
    norm_num at bound
  have rateNe:(c).value/2-1/2≠0 := by
    intro same
    apply ne
    linear_combination 2*same
  congr 1
  field_simp [ne,rateNe]

/-- One source equation retains the full physical field and both current B outside feet. -/
theorem original_reverse_R_full :
    R c z=((-(FiniteMobiusResolventFlux.actualMean z)/((c).value-1)) • G:BurnolL2)+
      burnolAmbientEvenPart
        (E (GenericSourceStepBAction.secondNext (barC c) (fourierL2 z):Hq)+
          fourierL2 (E (GenericSourceStepBAction.firstNext (barC c) (fourierL2 z):Hq))) := by
  have even:=inward_even c z (reverse_even c observation.mathlibZero)
  have part:burnolAmbientEvenPart (R c z)=R c z := by
    unfold burnolAmbientEvenPart
    rw [even]
    module
  have projection:=burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (R c z)
  change (Pi (R c z):BurnolL2)=burnolAmbientEvenPart (R c z)-
    burnolAmbientEvenMeanZeroCorrection (R c z) at projection
  rw [part,original_reverse_R_physical observation nontrivial half] at projection
  unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection at projection
  rw [(original_reverse_source_R_B observation nontrivial half).1,
    (original_reverse_source_R_B observation nontrivial half).2] at projection
  simp only [SetLike.val_smul] at projection
  linear_combination (norm:=module) -projection

private def reverseCoreRCurrent (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) (h:ℝ) : BurnolL2 :=
  (2*gamma coordinate) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction coordinate h
      (elementaryReverseSource (barC coordinate) (conjugate_zero coordinate zero))-
    (2*gamma (barC coordinate)) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction coordinate h
      (elementaryReverseSource coordinate zero)-
    (((coordinate.value-star coordinate.value)*gamma (barC coordinate))*(1/2:ℂ)) •
      (R coordinate (OriginalKExteriorCoPoissonAction.FullUnit.fullReverse coordinate h 1)-
        R coordinate (fourierL2 (OriginalKExteriorCoPoissonAction.FullUnit.fullForward coordinate h 0)))

/-- The fixed-h reverse programme consumes the new source equation with both full loss/unit feet. -/
theorem original_fixed_reverse_R_update :
    (((c).value-star (c).value)*gamma (barC c)) •
      R c (coreReverseSource c observation.mathlibZero (Real.log stageZeroSonineQ))=
      reverseCoreRCurrent c observation.mathlibZero (Real.log stageZeroSonineQ) := by
  let h:=Real.log stageZeroSonineQ
  have source:=reverse_R_equation c observation.mathlibZero
  have acted:=congrArg (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h) source
  have commute:=OriginalKFixedBoundarySourceFibre.finiteBoundaryAction_R c h z
  change R c (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h z)=
    OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (R c z) at commute
  have boundary:
      (((c).value-star (c).value)*gamma (barC c)) •
        R c (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h z)=
      (2*gamma c) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h
        (elementaryReverseSource (barC c) (conjugate_zero c observation.mathlibZero))-
      (2*gamma (barC c)) • OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h z := by
    rw [commute]
    unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction at acted ⊢
    simp only [map_smul,map_sub,smul_sub,smul_add,smul_smul] at acted ⊢
    linear_combination (norm:=module) acted
  change _=reverseCoreRCurrent c observation.mathlibZero h
  unfold coreReverseSource reverseCoreRCurrent
  rw [map_sub,map_smul,map_sub,smul_sub,smul_smul,boundary]

/-- The independent finite reverse source reaches that same complete computed R effect. -/
theorem original_fixed_source_R_programme :
    Tendsto (fun N:Nat=>(((c).value-star (c).value)*gamma (barC c)) •
      R c (DualSource.source N (OriginalKCoefficientBFiniteAction.sourceCore c (Real.log stageZeroSonineQ)))) atTop
      (𝓝 (reverseCoreRCurrent c observation.mathlibZero (Real.log stageZeroSonineQ))) := by
  have nn:0≤Real.log stageZeroSonineQ := Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have source:=core_reverse_tendsto c observation.mathlibZero (Real.log stageZeroSonineQ) nn
  have actual:=(((R c).continuous.tendsto _).comp source).const_smul
    (((c).value-star (c).value)*gamma (barC c))
  rw [original_fixed_reverse_R_update observation nontrivial half] at actual
  exact actual

end OriginalReverseSourceRTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
