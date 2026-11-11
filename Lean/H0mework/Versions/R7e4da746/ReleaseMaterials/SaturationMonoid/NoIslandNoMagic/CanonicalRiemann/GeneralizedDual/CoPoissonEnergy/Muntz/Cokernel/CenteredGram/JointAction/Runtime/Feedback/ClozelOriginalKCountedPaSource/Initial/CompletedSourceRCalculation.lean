import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.PaCoefficientSourceGramConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalCalculatedSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResidualRNativeSuccessor.Projection

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CompletedSourceRCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace Q
export PaCoefficientSourceGram
 (SourceSpace completedSource generatedPa sourceValue sourceWriter
  finiteCalculation physicalSynthesis sigmaSynthesis sigma_landing_read generated_pa_source
 )
export PaCoefficientSourceGramConsumer
 (returnCoefficient prefixProgramme actual_original_prefix actual_original_next original_pi_read)
end Q
namespace D
export OriginalKDirectRCofinalCalculatedSource
 (calculationRoot calculationCurrent actual_material_source_payload source_payload_literal)
end D
namespace Original
export OriginalKCombReceiptFeedback (Value Var receipt)
export OriginalBoundaryGammaTerminalConsumer
 (parentTrace originalChild originalOccurrence original_word currentPrefixReceipt currentPrefixTrace
  currentPrefix current_word_source original_address original_position originalWholeNext)
end Original
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree
 (Raw runtimeCurrent)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation
 (ResultAt resultAt sourceMaterialAt source_value)
end I
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
 (targetState target_expression trace value value_source relation_boundary updated_inverse_fibre original_material)
end C
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation
 (frontier realization normal completed targetRuntime completed_value target_factorizes)
end Calc
end OF

local instance : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

inductive Slot | source | physical | branches
abbrev Value : Slot → Type
 | .source => Q.SourceSpace
 | .physical => BurnolL2
 | .branches => OriginalKSourceResidualRNativeSuccessor.SourceBranches
abbrev Var (_:Slot) := Unit
instance groups : ∀s,AddCommGroup (Value s) := by
 intro s
 cases s <;> infer_instance

/-- The completed arithmetic source is realized before any physical R operation. -/
def physicalRealization : Q.SourceSpace →L[ℂ] BurnolL2 :=
 (evenBurnolClosedFace burnolUnscaledCommonGapRadius).subtypeL.comp
  (SourceGeneratedComplexFeaturePerfectification.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding)

def physicalCode : Expr Value Var .physical :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.source) (t:=Slot.physical) physicalRealization.toLinearMap.toAddMonoidHom (.var ())
def sigmaCode : Expr Value Var .physical :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.source) (t:=Slot.physical) Q.sourceWriter.toLinearMap.toAddMonoidHom (.var ())

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

def amplitudeCode : Expr Value Var .physical :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.physical) (t:=Slot.physical)
  (Q.returnCoefficient observation nontrivial half • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom physicalCode

def prefixCode : Expr Value Var .physical :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.physical) (t:=Slot.physical)
  ((burnolDirectRightResolventCLM c)^m).toLinearMap.toAddMonoidHom
  (amplitudeCode observation nontrivial half)

def inputCode : Expr Value Var .branches :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.physical) (t:=Slot.branches) OriginalKDefectAction.actionFields.toLinearMap.toAddMonoidHom
  (prefixCode observation nontrivial half)

def paCode : Expr Value Var .branches :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.branches) (t:=Slot.branches)
  (OriginalKFullSourceRAction.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
  (Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.branches) (t:=Slot.branches)
   OriginalKSourceResidualRNativeSuccessor.sourcePaInput.toLinearMap.toAddMonoidHom
   (inputCode observation nontrivial half))
def nonPaCode : Expr Value Var .branches :=
 Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.branches) (t:=Slot.branches)
  (OriginalKFullSourceRAction.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
  (Expr.linear (Value:=Value) (Var:=Var) (s:=Slot.branches) (t:=Slot.branches)
   OriginalKSourceResidualRNativeSuccessor.sourceNonPaInput.toLinearMap.toAddMonoidHom
   (inputCode observation nontrivial half))
def code : Expr Value Var .branches :=
 .add (paCode observation nontrivial half) (nonPaCode observation nontrivial half)

local instance originalSourceGroups (grade:Nat) : ∀target,AddCommGroup
 (OriginalKDirectRCofinalMaterial.L.Value (PairValue Original.Value) grade target) :=
 OriginalKDirectRCofinalMaterial.L.groups (PairValue Original.Value) grade

variable (depth ordinal:Nat)
def environment : Env Value Var
 | .source,_ => Q.completedSource c
 | .physical,_ => (Original.receipt observation nontrivial depth half).1.environment () ()
 | .branches,_ => 0

def raw : OF.Raw (Value:=Value) (Var:=Var) (sort:=Slot.branches) :=
 ⟨environment observation nontrivial half depth,code observation nontrivial half⟩

abbrev root := D.calculationRoot observation nontrivial half depth ordinal
abbrev current := D.calculationCurrent observation nontrivial half depth ordinal
abbrev point := (root observation nontrivial half depth ordinal).emitted
 (current observation nontrivial half depth ordinal)
def reader := fun {now}
 (_:(root observation nontrivial half depth ordinal).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) =>
 raw observation nontrivial half depth

def result : OF.I.ResultAt (root observation nontrivial half depth ordinal)
 (reader observation nontrivial half depth ordinal) (current:=current observation nontrivial half depth ordinal)
 (point observation nontrivial half depth ordinal) :=
 OF.I.resultAt (root observation nontrivial half depth ordinal)
  (reader observation nontrivial half depth ordinal) (current:=current observation nontrivial half depth ordinal)
  (point observation nontrivial half depth ordinal)
abbrev value := OF.C.value (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev paidState := OF.C.targetState (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev frontier := OF.Calc.frontier (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev realization := OF.Calc.realization (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev normal := OF.Calc.normal (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev completion := OF.Calc.completed (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)
abbrev normalized := OF.C.target_expression (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)

private def normalizedTrace (env:Env Value Var) (body:Expr Value Var Slot.branches)
 (state:SourceOperationExecutionDebt.State env body) (total:Value Slot.branches)
 (same:state.1=.const total) : Trace env body (.const total) :=
 Eq.mp (congrArg (fun terminal=>Trace env body terminal) same) state.2

private def normalizedAt {Network:WorldRelationNetwork} {Vocabulary':Vocabulary}
 (original:SourceNativeAuthoritativeRootClosure Network Vocabulary') (originCurrent:Vocabulary'.Current)
 (input:OF.Raw (Value:=Value) (Var:=Var) (sort:=Slot.branches)) :
 Trace input.environment input.expression (.const (OF.C.value original originCurrent (fun _=>input))) :=
 normalizedTrace input.environment input.expression (OF.C.targetState original originCurrent (fun _=>input))
  (OF.C.value original originCurrent (fun _=>input)) (OF.C.target_expression original originCurrent (fun _=>input))

def actualTrace := normalizedAt (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (raw observation nontrivial half depth)

def split := (actualTrace observation nontrivial half depth ordinal).splitAdd
def paReceipt : Trace.SourceReceipt (actualTrace observation nontrivial half depth ordinal)
 (paCode observation nontrivial half) :=
 ⟨(split observation nontrivial half depth ordinal).leftValue,
  (split observation nontrivial half depth ordinal).leftTrace,
  .left (split observation nontrivial half depth ordinal) (.refl _)⟩
def nonPaReceipt : Trace.SourceReceipt (actualTrace observation nontrivial half depth ordinal)
 (nonPaCode observation nontrivial half) :=
 ⟨(split observation nontrivial half depth ordinal).rightValue,
  (split observation nontrivial half depth ordinal).rightTrace,
  .right (split observation nontrivial half depth ordinal) (.refl _)⟩

theorem two_child_addresses :
 (paReceipt observation nontrivial half depth ordinal).retained.address=[0] ∧
 (nonPaReceipt observation nontrivial half depth ordinal).retained.address=[1] := ⟨rfl,rfl⟩
theorem two_child_sum : value observation nontrivial half depth ordinal=
 (paReceipt observation nontrivial half depth ordinal).value+
 (nonPaReceipt observation nontrivial half depth ordinal).value :=
 (split observation nontrivial half depth ordinal).total_eq

/-- This family is a mathematical source net, retained by the same dependent face. -/
def ArithmeticSourceData : Type :=
 (∀ F:Finset PaCoefficientSourceGram.Index,type_of% (PaCoefficientSourceGram.finiteCalculation c F)) ×
 Q.SourceSpace × type_of% (Q.generatedPa c) × BurnolL2 ×
 PLift (PaCoefficientSourceGram.Port.sourceMap (Q.generatedPa c)=Q.sourceValue c) ×
 (∀u:BurnolCompactCoPoissonLinearSource,PLift
  (PaCoefficientSourceGram.sigmaLanding u=burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactCoPoissonLanding u)))) ×
 (Nat→BurnolL2) × (Nat→ℂ) ×
 (∀k:Nat,PLift (PaCoefficientSourceGramConsumer.wholeProgramme c k=
  ((burnolDirectRightResolventCLM c)^k) (Q.generatedPa c:BurnolL2)))

def arithmeticSource : ArithmeticSourceData observation half :=
 (fun F=>PaCoefficientSourceGram.finiteCalculation c F,
  Q.completedSource c,Q.generatedPa c,Q.sourceValue c,
  PLift.up (Q.generated_pa_source c),
  fun u=>PLift.up (Q.sigma_landing_read u),
  PaCoefficientSourceGramConsumer.wholeProgramme c,PaCoefficientSourceGram.sourceMoment c,
  fun k=>PLift.up (PaCoefficientSourceGramConsumer.whole_programme_actual c k))

def sourceLaw : SourceNativeProjectionLaw
 (root observation nontrivial half depth ordinal).source.restructuringSource.toLedgerSource where
 Projection:=PUnit
 ActiveAt:=fun _ {_} _=>PUnit
 InactiveAt:=fun _ {_} _=>PEmpty
 classify:=fun _ {_} _=>.inl PUnit.unit
 PayloadAt:=fun _ {_} supplied _=>PProd (type_of% (arithmeticSource observation half))
  (OF.I.ResultAt (root observation nontrivial half depth ordinal)
   (reader observation nontrivial half depth ordinal) supplied)
 project:=fun _ {_} supplied _=>⟨arithmeticSource observation half,
  OF.I.resultAt (root observation nontrivial half depth ordinal)
   (reader observation nontrivial half depth ordinal) supplied⟩

abbrev originalLivingRoot := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
 (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.1.1
 (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.2.1
abbrev installed := (originalLivingRoot observation nontrivial half depth ordinal).withProjectionCoface
 (sourceLaw observation nontrivial half depth ordinal)
theorem installed_ledger : (installed observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot=
 (root observation nontrivial half depth ordinal).toLedgerRoot := rfl

def installedVisit : SourceNativeTemporalVisitAt
 (installed observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit
  (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.1.1
  (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.2.1

def sourceFace : SourceNativeRootSemanticFaceAt (installed observation nontrivial half depth ordinal)
 (installedVisit observation nontrivial half depth ordinal) where
 projection:=(SourceNativeProjectionLaw.InstallationAt.componentCoface
  (originalLivingRoot observation nontrivial half depth ordinal).source.base
  (sourceLaw observation nontrivial half depth ordinal)).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl

theorem source_face_read : (sourceFace observation nontrivial half depth ordinal).rootRead=
 PProd.mk (arithmeticSource observation half) (result observation nontrivial half depth ordinal) := rfl

theorem actual_source_material : (result observation nontrivial half depth ordinal).2.2.2=
 OF.I.sourceMaterialAt (root observation nontrivial half depth ordinal)
 (point observation nontrivial half depth ordinal) := rfl

theorem physical_source : physicalCode.eval (environment observation nontrivial half depth)=
 (Q.generatedPa c:BurnolL2) := rfl

theorem sigma_source : sigmaCode.eval (environment observation nontrivial half depth)=Q.sourceValue c := rfl

theorem prefix_source : (prefixCode observation nontrivial half).eval
 (environment observation nontrivial half depth)=PaCoefficientSourceGramConsumer.prefixProgramme observation nontrivial half m := by
 change ((burnolDirectRightResolventCLM c)^m)
  (Q.returnCoefficient observation nontrivial half • physicalRealization (Q.completedSource c))=_
 rw [map_smul,PaCoefficientSourceGramConsumer.prefixProgramme,PaCoefficientSourceGramConsumer.whole_programme_actual]
 rfl

theorem actual_source_value : value observation nontrivial half depth ordinal=
 (code observation nontrivial half).eval (environment observation nontrivial half depth) :=
 OF.C.value_source (root observation nontrivial half depth ordinal)
  (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)

abbrev actual_equation := OF.C.relation_boundary (R:=ℤ)
 (root observation nontrivial half depth ordinal) (current observation nontrivial half depth ordinal)
 (fun _=>raw observation nontrivial half depth)
abbrev whole_next := OF.Calc.target_factorizes (root observation nontrivial half depth ordinal)
 (current observation nontrivial half depth ordinal) (fun _=>raw observation nontrivial half depth)

end CountedPaInitial.CompletedSourceRCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
