import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ReturnResponse.Defect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalReturnResponseSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export OriginalColumnMomentSource.Prior (coordinate coordinate_value originalK)
end Prior

 def retainedEtaAction (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(Paid.Rplus (star coordinate.value/2)
    (burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (fourierL2 (OriginalColumnMomentSource.wholeContactResponse coordinate)))))+
  generatedReturnDefect coordinate-
  (2*(star coordinate.value-1/2)*Kernel.beta coordinate) •
    Paid.Rplus (star coordinate.value/2) (Paid.D (OriginalRieszFiniteSource.fourierPrimitive coordinate))

 theorem original_eta_remaining_action (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.Rplus (star coordinate.value/2) (OriginalColumnMomentSource.etaRemainingSource coordinate)=retainedEtaAction coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  unfold OriginalColumnMomentSource.etaRemainingSource retainedEtaAction
  have sourceAdd (left rightField : BurnolL2) : Paid.Rplus (star coordinate.value/2) (left+rightField)=
      Paid.Rplus (star coordinate.value/2) left+Paid.Rplus (star coordinate.value/2) rightField := by
    have actual := FiniteMobiusResolventFlux.Rplus_sub (star coordinate.value/2) right left (-rightField)
    rw [show left- -rightField=left+rightField by module] at actual
    have negative := FiniteMobiusResolventFlux.Rplus_smul (star coordinate.value/2) (-1) right rightField
    simp only [neg_one_smul] at negative
    rw [negative] at actual
    simpa only [sub_neg_eq_add] using actual
  rw [FiniteMobiusResolventFlux.Rplus_sub _ right,sourceAdd,FiniteMobiusResolventFlux.Rplus_smul _ _ right]
  have negative := FiniteMobiusResolventFlux.Rplus_smul (star coordinate.value/2) (-1) right
    (burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (fourierL2 (OriginalColumnMomentSource.wholeContactResponse coordinate))))
  simp only [neg_one_smul] at negative
  rw [negative,original_return_defect_occurrence]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def completeReturnPrice (h : ℝ) : ℂ :=
  -inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (Paid.D (FiniteMobiusResolventFlux.S.contactCorrection (Prior.coordinate observation nontrivial half)))-
  (1/2:ℂ)*(OriginalColumnMomentSource.generatedResponseRead (Prior.coordinate observation nontrivial half) h+
    inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
      (retainedEtaAction (Prior.coordinate observation nontrivial half)))+
  inner ℂ (OriginalColumnMomentSource.Paid.pairedColumn (Prior.coordinate observation nontrivial half) h)
    (OriginalColumnMomentSource.S.inverseAction (observation.coordinate/2) (star observation.coordinate/2)
      (OriginalColumnMomentSource.contactFluxSource observation nontrivial half))-
  FiniteMobiusResolventFlux.sourceA observation*
    OriginalColumnMomentSource.sourceBandPrice (Prior.coordinate observation nontrivial half)
      (fourierL2 (Prior.originalK observation nontrivial half)) h

theorem original_complete_return_price (h : ℝ) :
    OriginalColumnMomentSource.completeSourcePrice observation nontrivial half h=completeReturnPrice observation nontrivial half h := by
  unfold OriginalColumnMomentSource.completeSourcePrice OriginalColumnMomentSource.sourceContactPrice completeReturnPrice
  have source := original_eta_remaining_action (Prior.coordinate observation nontrivial half)
  rw [Prior.coordinate_value] at source
  rw [source]

theorem original_correction_return_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) h=
      -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) h
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-h)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeReturnPrice observation nontrivial half h) := by
  rw [OriginalColumnMomentSource.original_correction_source_price _ _ _ _ nonnegative bounded,original_complete_return_price]

theorem original_fixed_residual_return_price :
    -burnolPaFixedShiftResidual (Prior.coordinate observation nontrivial half)
      (by rw [Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (Prior.coordinate observation nontrivial half)-
      (1/2:ℂ)*star
        (OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-(Real.log stageZeroSonineQ))
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        completeReturnPrice observation nontrivial half (Real.log stageZeroSonineQ)) := by
  rw [OriginalColumnMomentSource.original_fixed_residual_source_price,original_complete_return_price]

end OriginalReturnResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
