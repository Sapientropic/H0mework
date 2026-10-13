import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Price
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Sources
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
namespace Paid
export FiniteMobiusResolventFlux (D)
end Paid

def starSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolCompletedMellinCoordinate :=
  OriginalPrimitiveRankBalance.conjugateCoordinate coordinate

def YMeanCoefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  Paid.sigma*(-Paid.actualMean (OriginalContactFeedbackSource.sourceForcing coordinate)/(star coordinate.value/2)-
    2*Paid.actualMean (OriginalContactFeedbackSource.sourceField coordinate))
def ErMeanCoefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  Paid.sigma*(-Paid.actualMean (OriginalReturnResponseSource.wholeReturnResponse coordinate)/(star coordinate.value/2)+
    2*Paid.actualMean (OriginalReturnResponseSource.correctedReturn coordinate))

-- Original paired support consumes the exterior source without erasing its full vector.
theorem original_Y_flux_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (burnolTateReciprocalL2 (Paid.actualFlux (star coordinate.value/2) (OriginalContactFeedbackSource.sourceForcing coordinate)))=
      YMeanCoefficient coordinate*inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h) (burnolTateReciprocalL2 (Paid.box 4)) := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [actual_forward_source_vector _ right,map_add,map_neg,map_smul,inner_add_right,inner_neg_right,inner_smul_right,paired_tate_outer_zero,
    original_Y_mean_response,neg_zero,zero_add]
  rfl

-- The actual original return fixes the reverse source mean; it is never supplied by the caller.
theorem original_Er_reverse_mean (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.actualMean (Paid.Rplus (star coordinate.value/2) (fourierL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate)))=
      -(2:ℂ)*Paid.actualMean (fourierL2 (OriginalReturnResponseSource.correctedReturn coordinate)) := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [← FiniteMobiusResolventFlux.fourier_R _ right,OriginalReturnResponseSource.original_R_return_response,map_smul,map_smul]
  rfl

def generatedErReverse (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (2*Paid.exteriorMoment (starSource coordinate) (fourierL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate))) • Paid.interiorBase (starSource coordinate)+
    (2*Paid.sigma*Paid.actualMean (fourierL2 (OriginalReturnResponseSource.correctedReturn coordinate))) • Paid.box 4+
    (Paid.sigma*Paid.actualMean (fourierL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate))) •
      OriginalPrimitiveRankBalance.boxSource (starSource coordinate)

def ErFluxPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h) (generatedErReverse coordinate)-
    ErMeanCoefficient coordinate*inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h) (burnolTateReciprocalL2 (Paid.box 4))

theorem original_Er_flux_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (Paid.defectFlux (star coordinate.value/2) (OriginalReturnResponseSource.wholeReturnResponse coordinate))=ErFluxPrice coordinate h := by
  have source := actual_direct_defect_flux_price coordinate (starSource coordinate) (OriginalReturnResponseSource.wholeReturnResponse coordinate)
    (original_return_response_even coordinate) h
  change inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
    (Paid.defectFlux (star coordinate.value/2) (OriginalReturnResponseSource.wholeReturnResponse coordinate))=_ at source
  rw [source]
  unfold generatedDirectFluxPrice ErFluxPrice
  have reverse : Paid.reverseRankSource (starSource coordinate) (fourierL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate))=
      generatedErReverse coordinate := by
    unfold Paid.reverseRankSource generatedErReverse
    have mean : Paid.actualMean (Paid.Rplus ((starSource coordinate).value/2) (fourierL2 (OriginalReturnResponseSource.wholeReturnResponse coordinate)))=
        -(2:ℂ)*Paid.actualMean (fourierL2 (OriginalReturnResponseSource.correctedReturn coordinate)) := original_Er_reverse_mean coordinate
    rw [mean,OriginalPrimitiveRankBalance.box_Rplus_source]
    module
  rw [reverse]
  change _-(generatedMeanCoefficient (star coordinate.value/2) (OriginalReturnResponseSource.wholeReturnResponse coordinate))*_=_
  rw [original_Er_mean_response]
  rfl
theorem actual_defectFlux_smul (z c : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    Paid.defectFlux z (c • value)=c • Paid.defectFlux z value := by
  have source := FiniteMobiusResolventFlux.actual_defect_R_action z right (c • value)
  rw [burnolDirectRightResolvent_smul z c] at source
  simp only [map_smul] at source
  rw [Paid.Rplus_smul z c right,
    FiniteMobiusResolventFlux.actual_defect_R_action z right value,smul_add] at source
  exact (add_left_cancel source).symm

 theorem actual_defectFlux_add (z : ℂ) (right : 1/4<z.re) (left rightValue : BurnolL2) :
    Paid.defectFlux z (left+rightValue)=Paid.defectFlux z left+Paid.defectFlux z rightValue := by
  have source := FiniteMobiusResolventFlux.actual_defect_R_action z right (left+rightValue)
  have Radd : burnolDirectRightResolvent z (left+rightValue)=burnolDirectRightResolvent z left+burnolDirectRightResolvent z rightValue := by
    have actual:=burnolDirectRightResolvent_sub z right left (-rightValue)
    have negative:=burnolDirectRightResolvent_smul z (-1) rightValue
    simp only [neg_one_smul] at negative
    simpa only [sub_neg_eq_add,negative] using actual
  have Padd : Paid.Rplus z (Paid.D left+Paid.D rightValue)=Paid.Rplus z (Paid.D left)+Paid.Rplus z (Paid.D rightValue) := by
    have actual:=Paid.Rplus_sub z right (Paid.D left) (-(Paid.D rightValue))
    have negative:=Paid.Rplus_smul z (-1) right (Paid.D rightValue)
    simp only [neg_one_smul] at negative
    simpa only [sub_neg_eq_add,negative] using actual
  rw [Radd,map_add,map_add,Padd,FiniteMobiusResolventFlux.actual_defect_R_action z right left,
    FiniteMobiusResolventFlux.actual_defect_R_action z right rightValue] at source
  have arranged : (Paid.Rplus z (Paid.D left)+Paid.Rplus z (Paid.D rightValue))+
      (Paid.defectFlux z left+Paid.defectFlux z rightValue)=
      (Paid.Rplus z (Paid.D left)+Paid.Rplus z (Paid.D rightValue))+Paid.defectFlux z (left+rightValue) := by
    rw [← source]
    module
  exact (add_left_cancel arranged).symm

open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export FiniteMobiusResolventFlux.Prior (coordinate coordinate_value originalK)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def jointContactInput : BurnolL2 :=
  -(FiniteMobiusResolventFlux.sourceA observation) • FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)+
    (1/2:ℂ) • FiniteMobiusResolventFlux.S.regularSource (Prior.coordinate observation nontrivial half)

theorem original_contact_flux_input :
    OriginalColumnMomentSource.contactFluxSource observation nontrivial half=
      Paid.defectFlux (observation.coordinate/2) (jointContactInput observation nontrivial half) := by
  have right := FiniteMobiusResolventFlux.Paid.parameter_rightQuarter observation half
  unfold OriginalColumnMomentSource.contactFluxSource jointContactInput
  rw [actual_defectFlux_add _ right,actual_defectFlux_smul _ _ right,actual_defectFlux_smul _ _ right]

 theorem original_contact_input_even : reflectL2 (jointContactInput observation nontrivial half)=jointContactInput observation nontrivial half := by
  unfold jointContactInput
  rw [map_add,map_smul,map_smul,original_contact_even,original_regular_even]

theorem original_contact_joint_R_source :
    burnolDirectRightResolvent (observation.coordinate/2) (jointContactInput observation nontrivial half)=
      (FiniteMobiusResolventFlux.sourceA observation) •
        burnolDirectRightResolvent (observation.coordinate/2) (Prior.originalK observation nontrivial half)-
      FiniteMobiusResolventFlux.S.correctedField (Prior.coordinate observation nontrivial half) := by
  have source := FiniteMobiusResolventFlux.Return.source_return_corrected_field observation nontrivial half
  change CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.R observation nontrivial half
    (FiniteMobiusResolventFlux.Return.sourceInput observation nontrivial half)=_ at source
  rw [FiniteMobiusResolventFlux.Paid.original_R_direct] at source
  have input : jointContactInput observation nontrivial half=
      (FiniteMobiusResolventFlux.sourceA observation) • Prior.originalK observation nontrivial half-
        FiniteMobiusResolventFlux.Return.sourceInput observation nontrivial half := by
    change -(FiniteMobiusResolventFlux.sourceA observation) • FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)+
      (1/2:ℂ) • FiniteMobiusResolventFlux.S.regularSource (Prior.coordinate observation nontrivial half)=
      (FiniteMobiusResolventFlux.sourceA observation) • Prior.originalK observation nontrivial half-
      (((star observation.coordinate-observation.coordinate)/2) •
        ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+
          FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half))-
        (1/2:ℂ) • FiniteMobiusResolventFlux.S.regularSource (Prior.coordinate observation nontrivial half))
    change -(FiniteMobiusResolventFlux.sourceA observation) • FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)+
      (1/2:ℂ) • FiniteMobiusResolventFlux.S.regularSource (Prior.coordinate observation nontrivial half)=
      (FiniteMobiusResolventFlux.sourceA observation) • (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)-
      (((star observation.coordinate-observation.coordinate)/2) •
        ((burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half):BurnolL2)+
          FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half))-
        (1/2:ℂ) • FiniteMobiusResolventFlux.S.regularSource (Prior.coordinate observation nontrivial half))
    unfold FiniteMobiusResolventFlux.sourceA
    module
  rw [input,burnolDirectRightResolvent_sub _ (FiniteMobiusResolventFlux.Paid.parameter_rightQuarter observation half),
    burnolDirectRightResolvent_smul,source]

def contactMeanCoefficient : ℂ :=
  Paid.sigma*(-Paid.actualMean (jointContactInput observation nontrivial half)/(observation.coordinate/2)-
    (FiniteMobiusResolventFlux.sourceA observation)*Paid.actualMean (burnolDirectRightResolvent (observation.coordinate/2)
      (Prior.originalK observation nontrivial half))+
    Paid.actualMean (FiniteMobiusResolventFlux.S.correctedField (Prior.coordinate observation nontrivial half)))

theorem original_contact_joint_mean :
    generatedMeanCoefficient (observation.coordinate/2) (jointContactInput observation nontrivial half)=
      contactMeanCoefficient observation nontrivial half := by
  unfold generatedMeanCoefficient contactMeanCoefficient
  rw [original_contact_joint_R_source,map_sub,map_smul]
  simp only [smul_eq_mul]
  ring

def contactJointPrice (h : ℝ) : ℂ :=
  OriginalPrimitiveRankBalance.twoMomentPrice (Prior.coordinate observation nontrivial half)
    (fourierL2 (jointContactInput observation nontrivial half)) h-
  contactMeanCoefficient observation nontrivial half*tateBoxInversePrice (Prior.coordinate observation nontrivial half) h

theorem original_contact_joint_price (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (OriginalPrimitiveRankBalance.inverseAction (observation.coordinate/2) (star observation.coordinate/2)
        (OriginalColumnMomentSource.contactFluxSource observation nontrivial half))=contactJointPrice observation nontrivial half h := by
  rw [original_contact_flux_input]
  have source:=actual_inverse_defect_flux_price (Prior.coordinate observation nontrivial half)
    (jointContactInput observation nontrivial half) (original_contact_input_even observation nontrivial half) h
  rw [Prior.coordinate_value] at source
  rw [source]
  unfold generatedInverseFluxPrice contactJointPrice
  change OriginalPrimitiveRankBalance.twoMomentPrice (Prior.coordinate observation nontrivial half) (fourierL2 (jointContactInput observation nontrivial half)) h-
    generatedMeanCoefficient (observation.coordinate/2) (jointContactInput observation nontrivial half)*tateBoxInversePrice (Prior.coordinate observation nontrivial half) h=_
  rw [original_contact_joint_mean]
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
