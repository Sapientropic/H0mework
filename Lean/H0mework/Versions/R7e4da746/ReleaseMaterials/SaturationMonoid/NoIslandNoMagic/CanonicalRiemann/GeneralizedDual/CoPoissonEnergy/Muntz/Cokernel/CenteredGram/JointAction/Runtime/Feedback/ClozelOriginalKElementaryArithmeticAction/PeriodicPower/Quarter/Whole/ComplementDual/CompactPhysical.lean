import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice
open OriginalKFiniteOrderRelease.UnitPowerSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "P" => burnolEvenAmbientProjection
local notation "Cq" => intervalConstant q
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem meanZero_extension_orthogonal (state:M):P (E (state:Hq))=0:=by
  change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto (E (state:Hq))=0
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  intro value inside
  rw [show E=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_right]
  exact (Submodule.mem_orthogonal _ _).mp state.property _ inside.1.1

theorem actual_compact_projection (state:Hq):
    P (E state)=burnolQuarterMeanCoefficient state • P (E Cq):=by
  have split:state=(Constructor.zeroMean state:Hq)+burnolQuarterMeanCoefficient state • Cq:=by
    rw [Constructor.zeroMean_read]
    module
  have source:=congrArg (fun t:Hq=>P (E t)) split
  rw [map_add,map_smul,map_add,map_smul,meanZero_extension_orthogonal,zero_add] at source
  exact source

/-- The actual compact counting source has precisely one physical Unit price, its complete mass. -/
theorem actual_count_physical_projection (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    P (fullFloorValue c zero)=
      burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero)) • P (E Cq):=by
  have source:=actual_compact_projection (Rq (fullFloorValue c zero))
  rw [actual_floor_compact c zero] at source
  exact source

private theorem projection_fourier (value:BurnolL2):
    P (fourierL2 value)=evenFaceFourierEquiv burnolUnscaledCommonGapRadius (P value):=by
  apply Subtype.ext
  exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius value).symm

/-- The whole shared field keeps the actual compact mass fee when its physical branch is read. -/
theorem actual_joint_physical_projection (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    P (fourierL2 (wholeValue c zero h positive)+fullFloorValue c zero)=
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius (P (wholeValue c zero h positive))+
        burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero)) • P (E Cq):=by
  rw [map_add,projection_fourier,actual_count_physical_projection]

private theorem physical_inner (test:BurnolPaAmbientCarrier) (value:BurnolL2):
    inner ℂ (test:BurnolL2) value=inner ℂ test (P value):=by
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left test value).symm

theorem actual_original_K_count_price (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (burnolCompletedMellinRieszVector d:BurnolL2) (fullFloorValue c zero)=
      burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero))*
        inner ℂ (burnolCompletedMellinRieszVector d:BurnolL2) (E Cq):=by
  rw [physical_inner (burnolCompletedMellinRieszVector d),actual_count_physical_projection,
    inner_smul_right,←physical_inner]

/-- The same original exact-m action is consumed after the joint physical projection, with its full Unit fee. -/
theorem actual_original_joint_physical_power (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m
        (P (fourierL2 (wholeValue c zero h positive)+fullFloorValue c zero):BurnolL2))=
      inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
        (CombSource.Division.rawIterate observation half.down m
          (fourierL2 (P (wholeValue c zero h positive):BurnolL2)))+
      burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero))*
        inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
          (CombSource.Division.rawIterate observation half.down m (P (E Cq):BurnolL2)):=by
  dsimp only
  rw [actual_joint_physical_projection]
  simp only [Submodule.coe_add,Submodule.coe_smul,map_add,map_smul,inner_add_right,inner_smul_right]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
