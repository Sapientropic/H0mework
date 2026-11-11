import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.PostDecoderRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalCommonAction.PostDecoder
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open SourceGeneratedScalarDifferentialResidual
namespace Tower
export ActualCofinalNativeTower
 (NativeValue Words CommonWords component nativeInventory stageInventory oldEnvironment actualIncrement updated_environment)
end Tower
variable {Sorts : Type u} {W X : Sorts→Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance adjacentGroups (grade : Nat) (target : Sorts) : AddCommGroup (T.Value W grade target) :=
 T.groups W grade target
variable (factory : T.Factory W X s) (initial : T.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : T.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s)) (language : cfg.LowVar=X)

/-- A full native value at an actual site of the existing future-invariant Model. -/
def siteRead (history : List PUnit.{u+1}) (ordinal : Nat) :
 Model factory initial cfg language →ₗ[ℤ] Tower.NativeValue factory initial cfg language ordinal s :=
 (additionReadout (R:=ℤ)).comp
  ((LinearMap.proj ordinal).comp (modelRead factory initial cfg language history))

theorem site_read_source (ordinal : Nat) (word : Tower.Words factory initial cfg language ordinal) :
 siteRead factory initial cfg language [] ordinal
  (projection factory initial cfg language (DFinsupp.single ordinal word))=
 evaluation (R:=ℤ) (site factory initial cfg language ordinal).2.1.1.activeEnvironment word := by
 change additionReadout (R:=ℤ)
  (modelRead factory initial cfg language []
   (projection factory initial cfg language (DFinsupp.single ordinal word)) ordinal)=_
 rw [model_read_source]
 change additionReadout (R:=ℤ)
  (Tower.nativeInventory factory initial cfg language ordinal
   (Tower.component factory initial cfg language ordinal (DFinsupp.single ordinal word)))=_
 simp only [Tower.component,DFinsupp.lapply_apply,DFinsupp.single_eq_same]
 exact (LinearMap.congr_fun (evaluation_update
  (Tower.oldEnvironment factory initial cfg language ordinal)
  (Tower.actualIncrement factory initial cfg language ordinal)) word).symm.trans
  (congrArg (fun environment=>evaluation (R:=ℤ) environment word)
   ((Tower.updated_environment factory initial cfg language ordinal).symm.trans
    (updated_environment_current factory initial cfg language ordinal)))

/-- Keep both actual occurrences and their distinct native grades in the same observer. -/
def adjacentRead (ordinal : Nat) : Model factory initial cfg language →ₗ[ℤ]
 (Tower.NativeValue factory initial cfg language ordinal s×
  Tower.NativeValue factory initial cfg language (ordinal+1) s) :=
 (siteRead factory initial cfg language [] ordinal).prod
  ((siteRead factory initial cfg language [] (ordinal+1)).comp (modelAction factory initial cfg language))

theorem adjacent_read_source (ordinal : Nat) (word : Tower.Words factory initial cfg language ordinal) :
 adjacentRead factory initial cfg language ordinal
  (projection factory initial cfg language (DFinsupp.single ordinal word))=
 (evaluation (R:=ℤ) (site factory initial cfg language ordinal).2.1.1.activeEnvironment word,
  evaluation (R:=ℤ) (site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
   (siteAction factory initial cfg language ordinal word)) := by
 apply Prod.ext
 · exact site_read_source factory initial cfg language ordinal word
 · change siteRead factory initial cfg language [] (ordinal+1)
    (modelAction factory initial cfg language
     (projection factory initial cfg language (DFinsupp.single ordinal word)))=_
   rw [model_action_source,action_source_word]
   exact site_read_source factory initial cfg language (ordinal+1) _

end ActualCofinalCommonAction.PostDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
