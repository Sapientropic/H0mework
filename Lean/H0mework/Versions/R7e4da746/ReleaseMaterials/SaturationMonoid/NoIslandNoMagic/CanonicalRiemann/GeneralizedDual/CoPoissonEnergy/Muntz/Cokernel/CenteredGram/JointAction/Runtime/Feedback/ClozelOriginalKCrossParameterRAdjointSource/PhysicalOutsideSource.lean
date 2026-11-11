import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalDefectSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open scoped InnerProductSpace
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible)
end PA
local instance physicalOutsideComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem outside_eq (value : BurnolL2) :
    outside value=value-(burnolEvenAmbientProjection value:BurnolL2) :=
  Submodule.starProjection_orthogonal_val value

private theorem physical_even (v : BurnolPaAmbientCarrier) : reflectL2 (v:BurnolL2)=v :=
  mem_evenL2ClosedFace_iff.mp v.property.2

private theorem Fourier_projection (value : BurnolL2) :
    (burnolEvenAmbientProjection (fourierL2 value):BurnolL2)=
      fourierL2 (burnolEvenAmbientProjection value:BurnolL2) :=
  (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius value).symm

private theorem Fourier_outside (value : BurnolL2) :
    fourierL2 (outside value)=outside (fourierL2 value) := by
  rw [outside_eq,outside_eq,map_sub,Fourier_projection]

private theorem original_R_Fourier_adjoint (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    fourierL2 (burnolDirectRightResolvent (c.value/2) value)=sourceAdjoint (barC c) (fourierL2 value) := by
  have parameter : star (barC c).value=c.value := star_star c.value
  unfold sourceAdjoint
  rw [parameter]
  exact FiniteMobiusResolventFlux.fourier_R (c.value/2)
    (by rw [Complex.div_re];norm_num;linarith [c.rightHalf]) value

/-- The whole physical input, with its true Fourier cotest, produces the complete outside vector. -/
theorem original_R_physical_outside_source (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    outside (burnolDirectRightResolvent (c.value/2) (v:BurnolL2))=
      (-2*inner ℂ (fourierL2 (generatedK c)) (v:BurnolL2)) • physicalOutsideColumn c := by
  let fv := evenFaceFourierEquiv burnolUnscaledCommonGapRadius v
  have amplitude : physicalAmplitude (barC c) fv=
      -2*inner ℂ (fourierL2 (generatedK c)) (v:BurnolL2) := by
    rw [←outsidePhysicalSource_read,outsidePhysicalSource,conjugate_twice,inner_smul_left]
    have paired := fourierL2.inner_map_map (generatedK c) (fourierL2 (v:BurnolL2))
    rw [fourierL2_fourierL2,physical_even] at paired
    change star (-2:ℂ)*inner ℂ (generatedK c) (fourierL2 (v:BurnolL2))=_
    rw [←paired]
    simp only [star_neg,star_ofNat]
  have defect := physical_adjoint_full_defect (barC c) fv
  change sourceAdjoint (barC c) (fourierL2 (v:BurnolL2))-
    (burnolEvenAmbientProjection (sourceAdjoint (barC c) (fourierL2 (v:BurnolL2))):BurnolL2)=_ at defect
  rw [←original_R_Fourier_adjoint,←outside_eq,amplitude] at defect
  rw [←Fourier_outside] at defect
  have reversed := congrArg fourierL2.symm defect
  rw [fourierL2.symm_apply_apply,map_smul] at reversed
  exact reversed

/-- This is the full physical block of the original R; no adjoint parameter replaces its occurrence. -/
theorem original_R_projected_outside_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    outside (burnolDirectRightResolvent (c.value/2) (burnolEvenAmbientProjection value:BurnolL2))=
      (-2*inner ℂ (fourierL2 (generatedK c)) (burnolEvenAmbientProjection value:BurnolL2)) •
        physicalOutsideColumn c :=
  original_R_physical_outside_source c (burnolEvenAmbientProjection value)

section ActualOriginalSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

/-- The actual Pa response already has the complete original physical qualification. -/
theorem actual_Pa_response_outside_zero (depth ordinal : Nat) :
    outside (OriginalKCombPhysicalAction.R observation nontrivial half
      (PA.E (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2))=0 := by
  have response := OriginalKDirectRCofinalDivision.source_response_value observation nontrivial half depth ordinal
  change (OriginalKDirectRCofinalDivision.sourceResponse observation nontrivial half depth ordinal:BurnolL2)=
    OriginalKCombPhysicalAction.R observation nontrivial half
      (PA.E (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2) at response
  rw [←response,outside_eq]
  have physical : burnolEvenAmbientProjection
      (OriginalKDirectRCofinalDivision.sourceResponse observation nontrivial half depth ordinal:BurnolL2)=
        OriginalKDirectRCofinalDivision.sourceResponse observation nontrivial half depth ordinal :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [physical,sub_self]

/-- Original n to n+1: the Pa foot is physically paid; Q and the entire outside inventory remain. -/
theorem actual_outside_successor_two_sources (depth ordinal : Nat) :
    outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1))=
      outside (burnolDirectRightResolvent (observation.coordinate/2)
        (outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal)))+
      (-2*inner ℂ (fourierL2 (generatedK c))
        (PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2)) •
        physicalOutsideColumn c := by
  let raw := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal
  have whole := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection raw)
  have inventory := congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2)) whole
  change (PA.E raw:BurnolL2)+(PA.Q raw:BurnolL2)=(burnolEvenAmbientProjection raw:BurnolL2) at inventory
  have full : raw=(PA.E raw:BurnolL2)+((PA.Q raw:BurnolL2)+outside raw) := by
    rw [outside_eq]
    linear_combination (norm := module) -inventory
  have action := congrArg outside
    (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal)
  change _=outside (OriginalKCombPhysicalAction.R observation nontrivial half raw) at action
  rw [full,map_add,map_add,map_add,map_add] at action
  rw [actual_Pa_response_outside_zero observation nontrivial half depth ordinal] at action
  simp only [zero_add] at action
  rw [OriginalKCombCofinalRAction.original_R_direct,OriginalKCombCofinalRAction.original_R_direct] at action
  have computed := original_R_physical_outside_source c (PA.Q raw)
  change outside (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q raw:BurnolL2))=
    (-2*inner ℂ (fourierL2 (generatedK c)) (PA.Q raw:BurnolL2)) • physicalOutsideColumn c at computed
  rw [computed] at action
  exact action.trans (add_comm _ _)

/-- Both full-vector faces come from the same original R successor and original source inventories. -/
theorem actual_Q_outside_coupled_sources (depth ordinal : Nat) :
    ((PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)):BurnolL2),
      outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)))=
    (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal •
        (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half:BurnolL2)+
      (PA.Q (burnolDirectRightResolvent (observation.coordinate/2)
        (PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2)):BurnolL2)+
      (-2*inner ℂ (hPowerPhysicalCorrection c)
        (outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal))) • generatedK (barC c),
      outside (burnolDirectRightResolvent (observation.coordinate/2)
        (outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal)))+
      (-2*inner ℂ (fourierL2 (generatedK c))
        (PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2)) •
        physicalOutsideColumn c) := by
  exact Prod.ext (actual_Q_successor_three_sources observation nontrivial half depth ordinal)
    (actual_outside_successor_two_sources observation nontrivial half depth ordinal)
end ActualOriginalSource

end OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
