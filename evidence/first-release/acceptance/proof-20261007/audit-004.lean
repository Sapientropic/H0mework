import H0mework.Papers.SourceProcessCoreAc
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.AdmissionAt", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.ActiveAt", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.InactiveAt", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Ledger", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Occurrence", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Readout", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.U7", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.World", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_answer", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_query", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.actual_next", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.actual_state", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.answerFace", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.authority", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.baseRoot", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.calculus", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.classify", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilation", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilationLaw", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compilationRoot", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.compiled", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumer", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumerLaw", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.consumerRoot", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointCount", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointInput", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointState", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpoint_source_state", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entry", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entryAt", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.entryAuthority", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.exactOccurrence", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.input", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.original", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.originalMaterialFace", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.original_material", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.packet", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.queryLaw", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.readout", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualEnvironment", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualFirstStep", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualMaterial", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualRegistered", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residualTarget", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_action", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.state", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit", "H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.actual_current", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.admission", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.authority", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpoint", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpointAuthority", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.endpointEntry", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.entry", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.initialEntry", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.initialRow", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.root", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.runtime", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.visit", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next", "H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actualRuntime", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actual_math_whole_next", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actual_normal_history", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actual_normal_value", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actual_query_answer_next", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.actual_source_material", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.generatedRuntime", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.Runtime.original_tree", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Runtime.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.actual_compiled", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.actual_tree", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.generatedInput", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.generatedState", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.inputState", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Input.queryInput", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.actual_next_material", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.current_whole_next", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.generated", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.generatedNext", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.nextRun", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.nextVisit", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.next_whole_next", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Next.query_answer_next", "H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Consumer")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "231c1cb7f92166c9880b05c9bdd580436ed5a5c6c1ae7669ec4e583ec8743bf0"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
