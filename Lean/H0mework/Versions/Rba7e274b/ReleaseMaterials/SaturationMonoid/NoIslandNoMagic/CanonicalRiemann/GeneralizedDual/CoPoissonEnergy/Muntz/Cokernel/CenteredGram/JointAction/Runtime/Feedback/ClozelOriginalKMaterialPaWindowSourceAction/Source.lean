import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Projection
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance paWindowComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace D
export OriginalKWholePaNativeRankSourceUpdate (SourceBranches SourceVar actualMaterialREffect actualMaterialInheritedREffect actual_material_R_effect_partition)
end D
namespace SF
export OriginalKWholePaNativeRankSourceUpdate.SourceFamily (Factory Packet)
end SF
namespace A
export OriginalKWholePaNativeRankSourceUpdate.SourceA (Programme)
end A
namespace L
export OriginalKWholePaNativeRankSourceUpdate.SourceL (Value groups)
end L
local instance paWindowGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
 L.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target
local notation "E" => OriginalKCombCofinalPaAction.E
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

def sourcePaMobius : D.SourceBranches →L[ℂ] BurnolL2 :=
 burnolMobiusSourceL2.comp ((OriginalKCombCofinalPaAction.E).comp OriginalKFullSourceRAction.originalField)

def sourcePaWindow (radius : ℝ) : D.SourceBranches →L[ℂ] BurnolRadiusIntervalL2 radius :=
 (burnolSourceOnlyCoPoissonWindow radius).comp sourcePaMobius

theorem source_pa_qualified (value : D.SourceBranches) :
 E (OriginalKFullSourceRAction.originalField value) ∈ burnolCompactCoPoissonClosedRange :=
 Submodule.starProjection_apply_mem _ _

theorem source_pa_window_generated (radius : ℝ) (value : D.SourceBranches) :
 sourcePaWindow radius value = burnolRadiusRestriction radius
  (E (OriginalKFullSourceRAction.originalField value) : BurnolL2) :=
 burnolSourceOnlyCoPoissonWindow_replay radius _ (source_pa_qualified value)

theorem source_pa_two_means (value : D.SourceBranches) :
 burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
   (E (OriginalKFullSourceRAction.originalField value)) =
  (-1/2:ℂ) * burnolSourceWindowIntegral (burnolTateReciprocalL2 (sourcePaMobius value)) ∧
 burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
   (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (E (OriginalKFullSourceRAction.originalField value))) =
  (-1/2:ℂ) * burnolSourceWindowIntegral (sourcePaMobius value) :=
 ⟨burnolPaPositionMean_from_source _ (source_pa_qualified value),
  burnolPaFourierMean_from_source _ (source_pa_qualified value)⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue OriginalKFullSourceRAction.C.Value) D.SourceVar ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue OriginalKFullSourceRAction.C.Value) (X:=D.SourceVar) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar:=D.SourceVar) (sort:=()))
variable (language : sourceCfg.LowVar=D.SourceVar)
variable (H N : ℝ)

def actualMaterialPaSource : BurnolL2 :=
 sourcePaMobius (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)

def actualMaterialPaWindow (radius : ℝ) : BurnolRadiusIntervalL2 radius :=
 sourcePaWindow radius (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)

theorem actual_material_Pa_window_generated (radius : ℝ) :
 actualMaterialPaWindow observation nontrivial half producer grade data sourceCfg language H N radius =
 burnolRadiusRestriction radius
  (E (OriginalKFullSourceRAction.originalField (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)) : BurnolL2) :=
 source_pa_window_generated radius _

theorem actual_material_Pa_window_keeps_inherited (radius : ℝ) :
 actualMaterialPaWindow observation nontrivial half producer grade data sourceCfg language H N radius =
 sourcePaWindow radius (D.actualMaterialInheritedREffect observation nontrivial half producer grade data sourceCfg language H N) +
 sourcePaWindow radius (OriginalKFullSourceRAction.variableAction observation nontrivial half
  (OriginalKWholePaNativeRankSourceUpdate.actualMaterialActorBranches observation nontrivial half producer grade data sourceCfg language H N)) := by
 unfold actualMaterialPaWindow
 rw [D.actual_material_R_effect_partition,map_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
