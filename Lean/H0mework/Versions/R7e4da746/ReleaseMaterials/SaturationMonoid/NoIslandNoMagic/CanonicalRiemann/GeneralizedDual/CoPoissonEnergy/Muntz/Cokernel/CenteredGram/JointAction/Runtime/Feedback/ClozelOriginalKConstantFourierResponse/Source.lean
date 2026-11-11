import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierResponseSource
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
open FixedWindowFourierReaction FixedWindowFourierReaction.FullSchur
namespace Prior
export OriginalConstantFourierNativeAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualTarget actualFrame)
end Prior
namespace C
export OriginalConstantFourierNativeConsumer
  (nextFace nextState nextValue nextQuarter next_state_source next_trace_source next_paid eta u forcing actual_full_equation actual_existing_inverse)
end C
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed
open private result_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource

local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "q" => (1/4:ℝ)

noncomputable def embed : M →L[ℂ] BurnolL2 :=
  burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)
noncomputable def read : BurnolL2 →L[ℂ] M := Constructor.zeroMean.comp burnolQuarterRestriction
noncomputable def center : BurnolL2 →L[ℂ] BurnolL2 := embed.comp read
noncomputable def inverse : BurnolL2 →L[ℂ] BurnolL2 :=
  embed.comp (burnolMeanZeroBlockInverse.comp read)

private theorem zeroMean_fixed (value:M) : Constructor.zeroMean (value:Hq)=value := by
  apply Subtype.ext
  rw [Constructor.zeroMean_read,Constructor.mean_zero,zero_smul,sub_zero]

private theorem read_embed (value:M) : read (embed value)=value := by
  change Constructor.zeroMean (burnolQuarterRestriction (burnolQuarterZeroExtension (value:Hq)))=value
  rw [burnolQuarterRestriction_zeroExtension,zeroMean_fixed]

private theorem inverse_center (value:BurnolL2) :
    inverse (center value)=embed (burnolMeanZeroBlockInverse (read value)) := by
  change embed (burnolMeanZeroBlockInverse (read (embed (read value))))=_
  rw [read_embed]

private def linear (operation:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body
noncomputable def etaCode : Prog.E := linear center (.var (0:Fin 2))
noncomputable def code : Prog.E := linear inverse etaCode

private abbrev Read {N:WorldRelationNetwork} {V:Vocabulary}
    (old:SourceNativeAuthoritativeRootClosure N V) :=
  {now:V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value:=Prog.Value) (Var:=Prog.Var) (sort:=())

namespace Generated
variable {N:WorldRelationNetwork} {V:Vocabulary}
variable (old:SourceNativeAuthoritativeRootClosure N V) (stage:V.Current) (input:BurnolL2)
noncomputable def environment : Env Prog.Value Prog.Var := fun _ _ => input
noncomputable def reader : Read old := fun {_} _ => ⟨environment input,code⟩
noncomputable def result : Installed.ResultAt old (reader old input) (old.emitted stage) :=
  Installed.resultAt old (reader old input) (old.emitted stage)
private theorem expression : type_of% (result_expression old (reader old input) (old.emitted stage)) :=
  result_expression old (reader old input) (old.emitted stage)
noncomputable def trace : Trace (environment input) code (.const ((result old stage input).2.2.1)) :=
  Eq.mp (congrArg (Trace (environment input) code) (expression old stage input)) (result old stage input).2.1.2
theorem trace_source : type_of% (mp_heq
    (congrArg (Trace (environment input) code) (expression old stage input)) (result old stage input).2.1.2) :=
  mp_heq _ _
noncomputable def inverseInput : Σ value:BurnolL2, Trace (environment input) etaCode (.const value) ×
    PLift (inverse value=(result old stage input).2.2.1) := originalInput (trace old stage input)
noncomputable def centerInput : Σ value:BurnolL2,
    Trace (environment input) (.var (0:Fin 2):Prog.E) (.const value) ×
      PLift (center value=(inverseInput old stage input).1) := originalInput (inverseInput old stage input).2.1
theorem input_binding : (centerInput old stage input).1=input := (centerInput old stage input).2.1.sound.symm
theorem equation : (result old stage input).2.2.1=inverse (center input) := (trace old stage input).sound.symm
theorem eta_actual : (inverseInput old stage input).1=center input := (inverseInput old stage input).2.1.sound.symm
theorem paid : (result old stage input).2.1.2.length=3 := Installed.source_history old (reader old input) (old.emitted stage)
end Generated

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)

local notation "baseRoot" => Prior.sourceRoot observation nontrivial half depth ordinal
local notation "baseVisit" => Prior.sourceVisit observation nontrivial half depth ordinal
local notation "baseU7" => Prior.sourceU7 observation nontrivial half depth ordinal
local notation "baseCalculus" => Prior.sourceCalculus observation nontrivial half depth ordinal
local notation "baseReader" => Prior.sourceReader observation nontrivial half depth ordinal t

noncomputable def sourceRoot := targetRoot baseRoot baseVisit baseU7 baseCalculus baseReader
noncomputable def sourceVisit := targetVisit baseRoot baseVisit baseU7 baseCalculus baseReader
private abbrev auth := (sourceRoot observation nontrivial half depth ordinal t).toAuthoritativeRoot
private abbrev current := (sourceVisit observation nontrivial half depth ordinal t).current
private abbrev point := (sourceRoot observation nontrivial half depth ordinal t).emitted
  (current observation nontrivial half depth ordinal t)
local notation "old" => auth observation nontrivial half depth ordinal t
local notation "now0" => current observation nontrivial half depth ordinal t
local notation "occurrence" => point observation nontrivial half depth ordinal t

noncomputable def inputFace := C.nextFace observation nontrivial half depth ordinal t
noncomputable def inputState := C.nextState observation nontrivial half depth ordinal t
noncomputable def inputValue : BurnolL2 := C.nextValue observation nontrivial half depth ordinal t

theorem source_frame_root : type_of% (frame_root baseRoot baseVisit baseU7 baseCalculus baseReader) :=
  frame_root baseRoot baseVisit baseU7 baseCalculus baseReader
theorem source_frame_visit : type_of% (frame_visit baseRoot baseVisit baseU7 baseCalculus baseReader) :=
  frame_visit baseRoot baseVisit baseU7 baseCalculus baseReader
theorem input_state_source : type_of% (C.next_state_source observation nontrivial half depth ordinal t) :=
  C.next_state_source observation nontrivial half depth ordinal t
theorem input_trace_source : type_of% (C.next_trace_source observation nontrivial half depth ordinal t) :=
  C.next_trace_source observation nontrivial half depth ordinal t

local notation "input" => inputValue observation nontrivial half depth ordinal t
noncomputable def environment := Generated.environment input
noncomputable def reader : Read old := Generated.reader old input
noncomputable def result := Generated.result old now0 input
noncomputable def trace := Generated.trace old now0 input
noncomputable def inverseInput := Generated.inverseInput old now0 input
noncomputable def centerInput := Generated.centerInput old now0 input

theorem trace_source : type_of% (Generated.trace_source old now0 input) := Generated.trace_source old now0 input
theorem input_binding : type_of% (Generated.input_binding old now0 input) := Generated.input_binding old now0 input
theorem equation : type_of% (Generated.equation old now0 input) := Generated.equation old now0 input
theorem eta_actual : (inverseInput observation nontrivial half depth ordinal t).1=
    embed (C.eta observation nontrivial half depth ordinal t) := Generated.eta_actual old now0 input

theorem u_actual : (result observation nontrivial half depth ordinal t).2.2.1=
    embed (C.u observation nontrivial half depth ordinal t) :=
  (equation observation nontrivial half depth ordinal t).trans
    (inverse_center (C.nextValue observation nontrivial half depth ordinal t))

noncomputable def quarterValue : Hq :=
  burnolQuarterRestriction (result observation nontrivial half depth ordinal t).2.2.1
theorem quarter_actual : quarterValue observation nontrivial half depth ordinal t=
    (C.u observation nontrivial half depth ordinal t:Hq) := by
  rw [quarterValue,u_actual]
  exact burnolQuarterRestriction_zeroExtension _

theorem paid : (result observation nontrivial half depth ordinal t).2.1.2.length=3 :=
  Generated.paid old now0 input

theorem actual_full_equation : quarterValue observation nontrivial half depth ordinal t-
    burnolTruncatedFourier (burnolTruncatedFourier (quarterValue observation nontrivial half depth ordinal t))=
      C.forcing observation nontrivial half depth ordinal t := by
  rw [quarter_actual]
  exact C.actual_full_equation observation nontrivial half depth ordinal t

theorem actual_existing_inverse : sourceInverse q
    (quarterChart (C.forcing observation nontrivial half depth ordinal t))=
      quarterChart (quarterValue observation nontrivial half depth ordinal t) :=
  (C.actual_existing_inverse observation nontrivial half depth ordinal t).trans
    (congrArg quarterChart (quarter_actual observation nontrivial half depth ordinal t).symm)

end OriginalConstantFourierResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierResponseSource"
