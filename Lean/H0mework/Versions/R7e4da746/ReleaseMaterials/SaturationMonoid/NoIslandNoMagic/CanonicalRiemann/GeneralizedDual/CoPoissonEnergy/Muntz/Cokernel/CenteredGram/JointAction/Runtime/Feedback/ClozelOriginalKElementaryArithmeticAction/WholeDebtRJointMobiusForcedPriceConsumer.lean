import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusForcedInverseSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusForcedPriceConsumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalWholeDebtRJointMobiusForcedInverseSource OriginalWholeDebtRJointMobiusCoupledCayleySource
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open scoped InnerProductSpace
open private source_Uadj_Kbar kernelMass from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.BPowerCayleySource
open private conjugate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusWholeLoopRSource
open private kernel_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveDilationSource
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "f" => calculatedForcing
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

/-- Every price leg is an actual complete forcing/K/B-source read; no response or terminal price is an input. -/
def nativeProgramme (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -((forcingDeterminant c : ℂ)⁻¹*
    (coupling c*inner ℂ (F (generatedK c)) (f (barC c))+
      star (coupling c)*inner ℂ (F (generatedK (barC c))) (f c)-
      (2*(sourceDamping (barC c) : ℂ)*((‖generatedK c‖^2 : ℝ) : ℂ))*
        inner ℂ (hPowerPhysicalCorrection (barC c)) (f c)))

/-- The whole U/F actions execute before the original K price is read. -/
theorem actual_source_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (generatedK c) (forcingResponse c)=-nativeProgramme c := by
  have adjoint:=source_Uadj_Kbar (barC c)
  rw [conjugate_twice,sourceCayley_actual_adjoint] at adjoint
  have first:=fourierL2.inner_map_map (F (generatedK c)) (f (barC c))
  rw [fourierL2_fourierL2,kernel_even] at first
  have second : inner ℂ (generatedK c) (sourceCayley (barC c) (f c))=
      star (coupling c)*inner ℂ (F (generatedK (barC c))) (f c)-
        (2*(sourceDamping (barC c) : ℂ)*((‖generatedK c‖^2 : ℝ) : ℂ))*
          inner ℂ (hPowerPhysicalCorrection (barC c)) (f c) := by
    rw [←ContinuousLinearMap.adjoint_inner_left,sourceCayley_actual_adjoint,adjoint,
      inner_sub_left,inner_smul_left,inner_smul_left,←actual_coupling]
    have realD : star (sourceDamping (barC c) : ℂ)=(sourceDamping (barC c) : ℂ) := Complex.conj_ofReal _
    have realM : star (kernelMass c)=((‖generatedK c‖^2 : ℝ) : ℂ) := Complex.conj_ofReal _
    simp only [map_mul,map_ofNat,starRingEnd_apply,realD,realM]
  unfold forcingResponse
  rw [inner_smul_right,inner_add_right,inner_smul_right,first,second]
  unfold nativeProgramme
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

/-- The original value and its unit are preserved as outputs of the complete new source calculation. -/
theorem actual_native_programme : nativeProgramme c=
    OriginalNextEndpointProgramme.programmePrice c (Real.log stageZeroSonineQ) := by
  rw [OriginalWholeDebtRJointMobiusUnitSource.actual_programme_price observation nontrivial half,
    ←generatedK_eq_original,←actual_forcing_response observation nontrivial half,actual_source_price,neg_neg]

def physicalInput : BurnolPaAmbientCarrier :=
  ⟨forcingInput c,by
    rw [actual_forcing_input observation nontrivial half]
    exact (OriginalWholeDebtRJointMobiusRActionSource.sourceInput observation nontrivial half).property⟩

private theorem input_price : inner ℂ (F (generatedK c)) (forcingInput c)=-nativeProgramme c := by
  rw [forcingInput,fourierL2.inner_map_map,actual_source_price]

/-- The independent original physical-R producer emits the full B field at the calculated original price. -/
theorem actual_native_B_effect : O (forcingNext c)=
    (2*nativeProgramme c) • physicalOutsideColumn c := by
  have action:=original_R_physical_outside_source c (physicalInput observation nontrivial half)
  change O (forcingNext c)=(-2*inner ℂ (F (generatedK c)) (forcingInput c)) • physicalOutsideColumn c at action
  rw [input_price observation nontrivial half] at action
  convert action using 1
  congr 1
  ring

theorem actual_native_whole_next : forcingNext c=
    (burnolEvenAmbientProjection (forcingNext c) : BurnolL2)+(2*nativeProgramme c) • physicalOutsideColumn c := by
  have whole : O (forcingNext c)=forcingNext c-(burnolEvenAmbientProjection (forcingNext c) : BurnolL2) :=
    Submodule.starProjection_orthogonal_val _
  rw [actual_native_B_effect observation nontrivial half] at whole
  linear_combination (norm:=module) -whole

/-- Energy is read on the actual physical input with its complete original B price. -/
theorem actual_native_energy : ‖forcingInput c‖^2-
    ‖forcingInput c+(sourceDamping c : ℂ) •
      (burnolEvenAmbientProjection (forcingNext c) : BurnolL2)‖^2=
    4*(sourceDamping c)^2*‖hPowerPhysicalCorrection (barC c)‖^2*‖nativeProgramme c‖^2 := by
  have action:=physical_forward_exact_loss c (physicalInput observation nontrivial half)
  change ‖forcingInput c‖^2-‖forcingInput c+(sourceDamping c : ℂ) •
    (burnolEvenAmbientProjection (forcingNext c) : BurnolL2)‖^2=
      4*(sourceDamping c)^2*‖hPowerPhysicalCorrection (barC c)‖^2*
        ‖inner ℂ (F (generatedK c)) (forcingInput c)‖^2 at action
  rw [input_price observation nontrivial half,norm_neg] at action
  exact action

theorem actual_native_programme_ne_zero : nativeProgramme c≠0 := by
  rw [actual_native_programme observation nontrivial half]
  exact OriginalWholeDebtRJointMobiusStrictSource.actual_programme_ne_zero observation nontrivial half

/-- Nonzero original K price excludes the false Pa splice for this actual source response. -/
theorem actual_forcing_response_not_Pa :
    ¬∃ physical : forcingResponse c∈evenBurnolClosedFace burnolUnscaledCommonGapRadius,
      (⟨forcingResponse c,physical⟩ : BurnolPaAmbientCarrier)∈burnolCompactCoPoissonClosedRange := by
  rintro ⟨physical,inside⟩
  have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have killed:=orthogonal ⟨forcingResponse c,physical⟩ inside
  have zero : inner ℂ (generatedK c) (forcingResponse c)=0 := by
    rw [generatedK_eq_original]
    exact inner_eq_zero_symm.mp killed
  rw [actual_source_price,neg_eq_zero] at zero
  exact actual_native_programme_ne_zero observation nontrivial half zero

end OriginalWholeDebtRJointMobiusForcedPriceConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
