import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Received
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Registered
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace Topology
open OriginalKPhysicalCorrectionStockSourceAction

/-- The generated mean-zero first and Fourier-second tail feet pay their physical cotest; the full ambient Tail remains. -/
theorem actual_source_correction_tail_physical_read (value : BurnolL2) (N : ℕ) (test : BurnolPaAmbientCarrier) :
 inner ℂ (actualPhysicalCorrectionTail value N) (test : BurnolL2) = 0 := by
 have first : inner ℂ
   (burnolQuarterZeroExtension (actualFirstCorrectionTail value N : BurnolQuarterIntervalL2)) (test : BurnolL2) = 0 := by
   unfold burnolQuarterZeroExtension burnolRadiusZeroExtension
   rw [ContinuousLinearMap.adjoint_inner_left,inner_eq_zero_symm]
   exact (actualFirstCorrectionTail value N).property _ test.property.1.1
 have even : reflectL2 (test : BurnolL2) = test := mem_evenL2ClosedFace_iff.mp test.property.2
 have twice : fourierL2 (fourierL2 (test : BurnolL2)) = test := by rw [fourierL2_fourierL2,even]
 have second : inner ℂ
   (fourierL2 (burnolQuarterZeroExtension (actualSecondCorrectionTail value N : BurnolQuarterIntervalL2)))
   (test : BurnolL2) = 0 := by
   calc
    _ = inner ℂ (fourierL2 (burnolQuarterZeroExtension (actualSecondCorrectionTail value N : BurnolQuarterIntervalL2)))
      (fourierL2 (fourierL2 (test : BurnolL2))) := by rw [twice]
    _ = inner ℂ (burnolQuarterZeroExtension (actualSecondCorrectionTail value N : BurnolQuarterIntervalL2))
      (fourierL2 (test : BurnolL2)) := Lp.inner_fourier_eq _ _
    _ = inner ℂ (actualSecondCorrectionTail value N : BurnolQuarterIntervalL2)
      (burnolQuarterRestriction (fourierL2 (test : BurnolL2))) := ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = 0 := by rw [inner_eq_zero_symm]; exact (actualSecondCorrectionTail value N).property _ test.property.1.2
 let raw := burnolQuarterZeroExtension (actualFirstCorrectionTail value N : BurnolQuarterIntervalL2) +
   fourierL2 (burnolQuarterZeroExtension (actualSecondCorrectionTail value N : BurnolQuarterIntervalL2))
 have rawZero : inner ℂ raw (test : BurnolL2) = 0 := by
   simp only [raw,inner_add_left,first,second,add_zero]
 have reflected : inner ℂ (reflectL2 raw) (test : BurnolL2) = 0 := by
   calc
    _ = inner ℂ (reflectL2 raw) (reflectL2 (test : BurnolL2)) := by rw [even]
    _ = inner ℂ raw (test : BurnolL2) := reflectL2.inner_map_map _ _
    _ = 0 := rawZero
 change inner ℂ (burnolAmbientEvenPart raw) (test : BurnolL2) = 0
 unfold burnolAmbientEvenPart
 rw [inner_smul_left,inner_add_left,rawZero,reflected]
 simp

local instance physicalReadGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

/-- The actual stored Tail is consumed through its same-source Trace; its physical zero is generated from both typed correction feet. -/
theorem actual_received_tail_physical_read (test : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalKFullSourceRAction.originalField (actualStoredPhysicalTail factory grade data sourceCfg language N))
   (test : BurnolL2) = 0 := by
 rw [(actual_received_physical_stock_and_tail factory grade data sourceCfg language N).2]
 change inner ℂ (sourcePhysicalTailAction N (OriginalKFullSourceRAction.originalField
   (actualMaterialStockSourceTotal factory grade data sourceCfg language N))) (test : BurnolL2) = 0
 rw [(source_physical_stock_actions_read _ N).2]
 exact actual_source_correction_tail_physical_read _ N test

/-- The current physical reader consumes the generated write itself, while inherited native change and full ambient Tail remain in their own inventory. -/
theorem actual_born_physical_read_consumes_source_write (name : sourceCfg.LowVar ()) (test : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalKFullSourceRAction.originalField
   (actualMaterialStockCompleteChange factory grade data sourceCfg language N name -
    actualMaterialStockInheritedChange factory grade data sourceCfg language N name)) (test : BurnolL2) =
 inner ℂ (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
   (actualMaterialStockSourceTotal factory grade data sourceCfg language N)) : BurnolL2) (test : BurnolL2) := by
 have source := congrArg OriginalKFullSourceRAction.originalField
   (actual_received_physical_projection_from_born factory grade data sourceCfg language N name)
 change (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
   (actualMaterialStockSourceTotal factory grade data sourceCfg language N)) : BurnolL2) = _ at source
 rw [source]
 simp only [map_sub,inner_sub_left]
 rw [actual_received_tail_physical_read,sub_zero]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
