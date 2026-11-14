import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Consumer

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Material
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
namespace CS
export BoundaryNativeKConductorSource (Source sub sub_gamma forward forward_gamma physical)
end CS
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (codeAt collapseValue)
end CF
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation (jointCode completeInput)
end FR
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
local instance groups (grade : Nat) (slot : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade slot) :=
  L.groups (PairValue C.Value) grade slot
local notation "total" => BoundaryNativeKAction.total

section Inventory
variable {V X : Unit → Type} [∀ slot, AddCommGroup (V slot)]
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := V) (Var := X) (sort := ()))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := ()))
variable (write : PairValue V () → Env (PairValue V) cfg.LowVar)

private theorem inventory_present :
    (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born frame cfg write).inventory.isSome=true := rfl

def inventorySeed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue V) cfg.LowVar ())) :=
  (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born frame cfg write).inventory.get
    (inventory_present frame cfg write)

theorem inventorySeed_source :
    (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born frame cfg write).inventory=some (inventorySeed frame cfg write) :=
  (Option.some_get (inventory_present frame cfg write)).symm
theorem born_next_environment
    (nextCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
      (PhysicalValue := PairValue V) (PhysicalVar := cfg.LowVar) (sort := ())) :
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born frame cfg write) nextCfg).activeEnvironment=
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born frame cfg write).activeEnvironment :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics.born_next_active
    (SourceGeneratedInquiryReceiptAction.Configured.Writeback.selected frame cfg write)
    (SourceGeneratedInquiryReceiptAction.Configured.Writeback.programme frame cfg write) nextCfg
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.rebase
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.configured_actual_paid_pair_writeback frame cfg write))
end Inventory

/-- The complete current source supplies the resolvent's two logarithmic graphs. -/
def resolve (coordinate : BurnolCompletedMellinCoordinate) (current : CS.Source) : CS.Source :=
  Math.scalar (sourceDamping coordinate : ℂ)⁻¹ (CS.sub (CS.forward coordinate current) current)

theorem resolve_value (coordinate : BurnolCompletedMellinCoordinate) (current : CS.Source) :
    (resolve coordinate current).value=burnolDirectRightResolventCLM coordinate current.value := by
  have live : (sourceDamping coordinate : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos coordinate).ne'
  change (sourceDamping coordinate : ℂ)⁻¹ • (sourceCayley coordinate current.value-current.value)=_
  rw [sourceCayley_apply,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ live,one_smul]
  rfl

theorem resolve_gamma (coordinate : BurnolCompletedMellinCoordinate) (current : CS.Source) :
    (resolve coordinate current).gamma=burnolDirectRightResolventCLM coordinate current.gamma := by
  have live : (sourceDamping coordinate : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos coordinate).ne'
  rw [resolve,Math.scalar_gamma,CS.sub_gamma,CS.forward_gamma,sourceCayley_apply,
    add_sub_cancel_left,smul_smul,inv_mul_cancel₀ live,one_smul]
  rfl

theorem total_collapse (grade : Nat) (row : PairValue (L.Value (PairValue C.Value) grade) ()) :
    total (grade+1) row=total 1 (CF.collapseValue grade row) := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change total (grade+1) row.1+total (grade+1) row.2=
      total 1 (CF.collapseValue grade (row.1+row.2))
    exact (map_add (total (grade+1)) row.1 row.2).symm.trans (previous (row.1+row.2))

theorem current_collapse (grade : Nat) (row : L.Value (PairValue C.Value) grade ()) :
    let _ : AddCommGroup (L.Value (PairValue C.Value) grade ()) := L.groups (PairValue C.Value) grade ()
    total 1 (CF.collapseValue grade (row,0))=total grade row := by
  dsimp only
  rw [←total_collapse]
  change total grade row+total grade _=total grade row
  simp only [AddMonoidHom.coe_snd,map_zero,add_zero]

theorem joint_total (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ j : Nat, observation.coordinate=-2*(j+1))
    (half : OriginalKCombCalculation.Half observation)
    (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    total 1 ((FR.jointCode (OriginalKCombPhysicalAction.code observation nontrivial half)).eval environment)=
      OriginalKCombPhysicalAction.R observation nontrivial half (total 1 (environment () ())) := by
  let result := (FR.jointCode (OriginalKCombPhysicalAction.code observation nontrivial half)).eval environment
  have sum : total 1 result=(result.1+result.2).1+(result.1+result.2).2 := by
    change (result.1.1+result.1.2)+(result.2.1+result.2.2)=
      (result.1.1+result.2.1)+(result.1.2+result.2.2)
    abel
  have input : (FR.completeInput environment () ()).1+(FR.completeInput environment () ()).2=total 1 (environment () ()) := by
    change ((environment () ()).1.1+(environment () ()).2.1)+
      ((environment () ()).1.2+(environment () ()).2.2)=
      ((environment () ()).1.1+(environment () ()).1.2)+
      ((environment () ()).2.1+(environment () ()).2.2)
    abel
  have action := (congrArg (fun pair : BurnolL2 × BurnolL2 => pair.1+pair.2)
    (OriginalKCombFullSourceDynamics.joint_complete_value observation nontrivial half environment)).trans
      (OriginalKCombFullResidualAction.split_complete _)
  rw [input] at action
  exact sum.trans action

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Material
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
