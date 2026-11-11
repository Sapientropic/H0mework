import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteContactPrice.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCompleteContactPriceProgram

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCompleteFeeSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Input
export OriginalCompleteFeeInput (sourceRoot sourceVisit source_frame_root source_frame_visit kernelValue kernelTrace bValue bTrace kernel_actual b_actual)
end Input
namespace P
export OriginalCompleteFeeProgram (code pairedCode defectCode environment code_eval paired_actual defect_eval code_actual code_budget)
end P
namespace M
export OriginalConstantFourierPriceMath (scalarRead scalarLift scalar_lift)
end M
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_value source_history)
end Installed
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
private abbrev Read {W:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure W V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())
namespace Generated
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure W V) (stage:V.Current)
variable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (kernel b:BurnolL2)
noncomputable def reader : Read old := fun {_} _=>⟨P.environment kernel b,P.code c h⟩
noncomputable def result : Installed.ResultAt old (reader old c h kernel b) (old.emitted stage) :=
  Installed.resultAt old (reader old c h kernel b) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old c h kernel b) (old.emitted stage)) :=
  result_expression old (reader old c h kernel b) (old.emitted stage)
noncomputable def trace : Trace (P.environment kernel b) (P.code c h)
    (.const ((result old stage c h kernel b).2.2.1)) :=
  Eq.mp (congrArg (Trace (P.environment kernel b) (P.code c h)) (expression old stage c h kernel b))
    (result old stage c h kernel b).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (P.environment kernel b) (P.code c h)) (expression old stage c h kernel b))
      (result old stage c h kernel b).2.1.2) := mp_heq _ _
theorem equation : (result old stage c h kernel b).2.2.1=(P.code c h).eval (P.environment kernel b) :=
  Installed.source_value old (reader old c h kernel b) (old.emitted stage)
theorem paid : (result old stage c h kernel b).2.1.2.length=24 :=
  (Installed.source_history old (reader old c h kernel b) (old.emitted stage)).trans (P.code_budget c h)
noncomputable def split := Trace.splitBilinear (trace old stage c h kernel b)
noncomputable def columnValue := (split old stage c h kernel b).leftValue
noncomputable def defectValue := (split old stage c h kernel b).rightValue
noncomputable def columnTrace := (split old stage c h kernel b).leftTrace
noncomputable def defectTrace := (split old stage c h kernel b).rightTrace
theorem column_equation : columnValue old stage c h kernel b=(P.pairedCode c h).eval (P.environment kernel b) :=
  (columnTrace old stage c h kernel b).sound.symm
theorem defect_equation : defectValue old stage c h kernel b=FiniteMobiusResolventFlux.D kernel :=
  (defectTrace old stage c h kernel b).sound.symm.trans (P.defect_eval (P.environment kernel b))
end Generated

private theorem recognize
    (observation:GeneratedRiemannZeroObservation)
    (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
    (half:OriginalKCombCalculation.Half observation) (h:ℝ)
    (nonnegative:0≤h) (bounded:h≤Real.log 2) (kernel b:BurnolL2)
    (kernelSource:kernel=(burnolCompletedMellinRieszVector
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half):BurnolL2))
    (bSource:b=burnolQuarterZeroExtension (burnolRieszSingleFourierSource
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half):BurnolQuarterIntervalL2)) :
    (P.code (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h).eval
      (P.environment kernel b)=M.scalarLift
        (OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h) := by
  rw [kernelSource,bSource]
  exact P.code_actual observation nontrivial half h nonnegative bounded

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
noncomputable def sourceRoot := Input.sourceRoot observation nontrivial half depth ordinal t
noncomputable def sourceVisit := Input.sourceVisit observation nontrivial half depth ordinal t
theorem source_frame_root : type_of% (Input.source_frame_root observation nontrivial half depth ordinal t) :=
  Input.source_frame_root observation nontrivial half depth ordinal t
theorem source_frame_visit : type_of% (Input.source_frame_visit observation nontrivial half depth ordinal t) :=
  Input.source_frame_visit observation nontrivial half depth ordinal t
private abbrev authority := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
local notation "old"=>authority observation nontrivial half depth ordinal t
local notation "now0"=>current observation nontrivial half depth ordinal t
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h"=>OriginalKBFiniteCalculation.fixedShift
local notation "kernel"=>Input.kernelValue observation nontrivial half depth ordinal t
local notation "b"=>Input.bValue observation nontrivial half depth ordinal t
noncomputable def reader : Read old := Generated.reader old c h kernel b
noncomputable def result := Generated.result old now0 c h kernel b
noncomputable def trace := Generated.trace old now0 c h kernel b
theorem trace_source : type_of% (Generated.trace_source old now0 c h kernel b) := Generated.trace_source old now0 c h kernel b
theorem equation : type_of% (Generated.equation old now0 c h kernel b) := Generated.equation old now0 c h kernel b
theorem paid : type_of% (Generated.paid old now0 c h kernel b) := Generated.paid old now0 c h kernel b
noncomputable def split := Generated.split old now0 c h kernel b
noncomputable def columnValue := Generated.columnValue old now0 c h kernel b
noncomputable def defectValue := Generated.defectValue old now0 c h kernel b
noncomputable def columnTrace := Generated.columnTrace old now0 c h kernel b
noncomputable def defectTrace := Generated.defectTrace old now0 c h kernel b
theorem column_equation : type_of% (Generated.column_equation old now0 c h kernel b) := Generated.column_equation old now0 c h kernel b
theorem defect_equation : type_of% (Generated.defect_equation old now0 c h kernel b) := Generated.defect_equation old now0 c h kernel b
private theorem fixed_nonnegative : 0≤h := by
  apply Real.log_nonneg
  change 1≤Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)
private theorem fixed_bounded : h≤Real.log 2 :=
  (le_abs_self h).trans OriginalRieszFiniteColumns.fixedShift_small
private theorem recognized : (P.code c h).eval (P.environment kernel b)=
    M.scalarLift (OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h) :=
  recognize observation nontrivial half h fixed_nonnegative fixed_bounded kernel b
    (Input.kernel_actual observation nontrivial half depth ordinal t)
    (Input.b_actual observation nontrivial half depth ordinal t)
theorem actual_output : (result observation nontrivial half depth ordinal t).2.2.1=
    M.scalarLift (OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h) :=
  (Generated.equation old now0 c h kernel b).trans (recognized observation nontrivial half depth ordinal t)
theorem actual_price : M.scalarRead ((result observation nontrivial half depth ordinal t).2.2.1)=
    OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h :=
  (congrArg M.scalarRead (actual_output observation nontrivial half depth ordinal t)).trans (M.scalar_lift _)
end OriginalCompleteFeeSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCompleteFeeSource"
