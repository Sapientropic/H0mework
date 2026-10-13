import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields source_fields_first)
end Native
namespace SF
export OriginalKWholePaNativeRankSourceUpdate.SourceFamily (Factory Packet)
end SF
namespace A
export OriginalKWholePaNativeRankSourceUpdate.SourceA (Programme)
end A
namespace L
export OriginalKWholePaNativeRankSourceUpdate.SourceL (Value groups)
end L
local instance paActionGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

def sourcePaSourceAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 Native.sourceFields.comp sourcePaMobius

def sourcePaCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) sourcePaSourceAction.toLinearMap.toAddMonoidHom (.var ())

def sourcePaEnvironment (value : D.SourceBranches) : Env (PairValue (PairValue C.Value)) C.Var := fun _ _ => value

def sourcePaRaw (value : D.SourceBranches) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (PairValue C.Value)) (Var:=C.Var) (sort:=()) :=
 ⟨sourcePaEnvironment value,sourcePaCode⟩

def sourcePaTrace (value : D.SourceBranches) :
 Trace (sourcePaRaw value).environment (sourcePaRaw value).expression
  (.const ((sourcePaRaw value).expression.eval (sourcePaRaw value).environment)) :=
 execution _ _

theorem source_pa_ast_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 sourcePaCode.effect environment increment = sourcePaSourceAction (increment () ()) := rfl

theorem source_pa_ast_source (value : D.SourceBranches) :
 OriginalKFullSourceRAction.originalField ((sourcePaRaw value).expression.eval (sourcePaRaw value).environment) =
 sourcePaMobius value := by
 change OriginalKFullSourceRAction.originalField (Native.sourceFields (sourcePaMobius value)) = _
 exact Native.source_fields_first _

theorem source_pa_ast_window (value : D.SourceBranches) (radius : ℝ) :
 burnolSourceOnlyCoPoissonWindow radius
  (OriginalKFullSourceRAction.originalField ((sourcePaRaw value).expression.eval (sourcePaRaw value).environment)) =
 burnolRadiusRestriction radius (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField value) : BurnolL2) := by
 rw [source_pa_ast_source]
 exact source_pa_window_generated radius value

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) D.SourceVar ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=D.SourceVar) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=D.SourceVar) (sort:=()))
variable (language : sourceCfg.LowVar=D.SourceVar)
variable (H N : ℝ)

def actualMaterialPaRaw :=
 sourcePaRaw (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)

def actualMaterialPaTrace :=
 sourcePaTrace (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)

theorem actual_material_source_ast_window (radius : ℝ) :
 burnolSourceOnlyCoPoissonWindow radius
  (OriginalKFullSourceRAction.originalField
   ((actualMaterialPaRaw observation nontrivial half producer grade data sourceCfg language H N).expression.eval
    (actualMaterialPaRaw observation nontrivial half producer grade data sourceCfg language H N).environment)) =
 burnolRadiusRestriction radius
  (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField
   (D.actualMaterialREffect observation nontrivial half producer grade data sourceCfg language H N)) : BurnolL2) :=
 source_pa_ast_window _ radius

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
