import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalCFixedAdjoint.Origin

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCFixedAdjointSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Root
export OriginalCFixedAdjointOrigin
  (sourceRoot sourceVisit source_frame_root source_frame_visit correctionValue correctionTrace correction_trace_source correction_actual)
end Root
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history source_value)
end Installed
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

noncomputable def operation (c:BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceCayley c).adjoint
noncomputable def code (c:BurnolCompletedMellinCoordinate) : Prog.E :=
  .linear (s:=()) (operation c).toLinearMap.toAddMonoidHom (.var (0:Fin 2))
theorem code_budget (c:BurnolCompletedMellinCoordinate) : remaining (code c)=2 := rfl

private abbrev Read {W:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure W V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())
namespace Generated
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure W V) (stage:V.Current)
variable (c:BurnolCompletedMellinCoordinate) (actual:BurnolL2)
noncomputable def environment : Env Prog.Value Prog.Var := fun _ _ => actual
noncomputable def reader : Read old := fun {_} _ => ⟨environment actual,code c⟩
noncomputable def result : Installed.ResultAt old (reader old c actual) (old.emitted stage) :=
  Installed.resultAt old (reader old c actual) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old c actual) (old.emitted stage)) :=
  result_expression old (reader old c actual) (old.emitted stage)
noncomputable def trace : Trace (environment actual) (code c) (.const ((result old stage c actual).2.2.1)) :=
  Eq.mp (congrArg (Trace (environment actual) (code c)) (expression old stage c actual))
    (result old stage c actual).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (environment actual) (code c)) (expression old stage c actual))
      (result old stage c actual).2.1.2) := mp_heq _ _
noncomputable def input := originalInput (trace old stage c actual)
theorem input_binding : (input old stage c actual).1=actual :=
  (input old stage c actual).2.1.sound.symm
theorem action : operation c (input old stage c actual).1=(result old stage c actual).2.2.1 :=
  (input old stage c actual).2.2.down
theorem equation : (result old stage c actual).2.2.1=operation c actual :=
  (action old stage c actual).symm.trans (congrArg (operation c) (input_binding old stage c actual))
theorem paid : (result old stage c actual).2.1.2.length=2 :=
  (Installed.source_history old (reader old c actual) (old.emitted stage)).trans (code_budget c)
end Generated

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
noncomputable def sourceRoot := Root.sourceRoot observation nontrivial half depth ordinal t
noncomputable def sourceVisit := Root.sourceVisit observation nontrivial half depth ordinal t
private abbrev auth := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
local notation "old" => auth observation nontrivial half depth ordinal t
local notation "now0" => current observation nontrivial half depth ordinal t
noncomputable def correctionValue := Root.correctionValue observation nontrivial half depth ordinal t
local notation "actualC" => correctionValue observation nontrivial half depth ordinal t
noncomputable def inputCorrectionTrace := Root.correctionTrace observation nontrivial half depth ordinal t
theorem input_trace_source : type_of% (Root.correction_trace_source observation nontrivial half depth ordinal t) :=
  Root.correction_trace_source observation nontrivial half depth ordinal t
theorem source_frame_root : type_of% (Root.source_frame_root observation nontrivial half depth ordinal t) :=
  Root.source_frame_root observation nontrivial half depth ordinal t
theorem source_frame_visit : type_of% (Root.source_frame_visit observation nontrivial half depth ordinal t) :=
  Root.source_frame_visit observation nontrivial half depth ordinal t

noncomputable def environment := Generated.environment actualC
noncomputable def reader : Read old := Generated.reader old c actualC
noncomputable def result := Generated.result old now0 c actualC
noncomputable def trace := Generated.trace old now0 c actualC
noncomputable def input := Generated.input old now0 c actualC
theorem trace_source : type_of% (Generated.trace_source old now0 c actualC) :=
  Generated.trace_source old now0 c actualC
theorem input_binding : type_of% (Generated.input_binding old now0 c actualC) :=
  Generated.input_binding old now0 c actualC
theorem action : type_of% (Generated.action old now0 c actualC) :=
  Generated.action old now0 c actualC
theorem equation : type_of% (Generated.equation old now0 c actualC) :=
  Generated.equation old now0 c actualC
theorem paid : type_of% (Generated.paid old now0 c actualC) :=
  Generated.paid old now0 c actualC
theorem actual_output : (result observation nontrivial half depth ordinal t).2.2.1=
    operation c (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c) :=
  (Generated.equation old now0 c actualC).trans
    (congrArg (operation c) (Root.correction_actual observation nontrivial half depth ordinal t))

end OriginalCFixedAdjointSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCFixedAdjointSource"
