import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedWaveActionSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
namespace Root
export OriginalKPairedWaveRootSource (sourceRoot sourceVisit waveValue waveTrace wave_trace_source wave_value)
end Root
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed

private theorem result_expression {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V)
    (rawReader : {now : V.Current} →
      old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
        O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()))
    {now : V.Current}
    (point : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    (Installed.resultAt old rawReader point).2.1.1 =
      .const ((Installed.resultAt old rawReader point).2.2.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression old now
    (fun _ => rawReader point)

def shift : ℝ := OriginalKBFiniteCalculation.fixedShift

private def linear (operation : BurnolL2 →L[ℂ] BurnolL2) (body : Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body

def dilationCode : Prog.E :=
  linear (pairedBurnolMultiplicativeDilation shift) (.var (0 : Fin 2))

def projectionCode : Prog.E :=
  linear burnolEvenAmbientProjectionEndomorphism dilationCode

def fourierCode : Prog.E :=
  linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap projectionCode

def code (c : BurnolCompletedMellinCoordinate) : Prog.E :=
  linear (burnolDirectRightResolventCLM c) fourierCode

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

abbrev sourceRoot := Root.sourceRoot observation nontrivial half depth ordinal
abbrev sourceVisit := Root.sourceVisit observation nontrivial half depth ordinal
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev sourceOccurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (sourceCurrent observation nontrivial half depth ordinal)
local notation "authority" => sourceAuthority observation nontrivial half depth ordinal
local notation "current" => sourceCurrent observation nontrivial half depth ordinal
local notation "occurrence" => sourceOccurrence observation nontrivial half depth ordinal

def environment : Env Prog.Value Prog.Var :=
  fun _ _ => Root.waveValue observation nontrivial half depth ordinal

/-- The current root supplies the retained scaled wave; each original operation gets its own Step. -/
def reader {now : (OriginalKOutsideCorrectionProjectionAction.actualTarget
    observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨environment observation nontrivial half depth ordinal, code c⟩

def result : Installed.ResultAt authority (reader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (reader observation nontrivial half depth ordinal) occurrence

private theorem expression : type_of% (result_expression authority
    (reader observation nontrivial half depth ordinal) occurrence) :=
  result_expression authority (reader observation nontrivial half depth ordinal) occurrence

def trace : Trace (environment observation nontrivial half depth ordinal) (code c)
    (.const ((result observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal)
    (code c) expression) (expression observation nontrivial half depth ordinal))
    (result observation nontrivial half depth ordinal).2.1.2

theorem trace_heq : type_of% (mp_heq
    (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal) (code c) expression)
      (expression observation nontrivial half depth ordinal))
    (result observation nontrivial half depth ordinal).2.1.2) :=
  mp_heq _ _

def rInput : Σ point : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) fourierCode (.const point) ×
    PLift (burnolDirectRightResolventCLM c point = (result observation nontrivial half depth ordinal).2.2.1) :=
  originalInput (trace observation nontrivial half depth ordinal)

def fourierInput : Σ point : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) projectionCode (.const point) ×
    PLift (fourierL2 point = (rInput observation nontrivial half depth ordinal).1) :=
  originalInput (rInput observation nontrivial half depth ordinal).2.1

def projectionInput : Σ point : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) dilationCode (.const point) ×
    PLift (burnolEvenAmbientProjectionEndomorphism point = (fourierInput observation nontrivial half depth ordinal).1) :=
  originalInput (fourierInput observation nontrivial half depth ordinal).2.1

def dilationInput : Σ point : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) (.var (0 : Fin 2) : Prog.E) (.const point) ×
    PLift (pairedBurnolMultiplicativeDilation shift point = (projectionInput observation nontrivial half depth ordinal).1) :=
  originalInput (projectionInput observation nontrivial half depth ordinal).2.1

theorem input_binding : (dilationInput observation nontrivial half depth ordinal).1 =
    Root.waveValue observation nontrivial half depth ordinal :=
  (dilationInput observation nontrivial half depth ordinal).2.1.sound.symm

theorem dilation_equation :
    pairedBurnolMultiplicativeDilation shift (dilationInput observation nontrivial half depth ordinal).1 =
      (projectionInput observation nontrivial half depth ordinal).1 :=
  (dilationInput observation nontrivial half depth ordinal).2.2.down

theorem projection_equation :
    burnolEvenAmbientProjectionEndomorphism (projectionInput observation nontrivial half depth ordinal).1 =
      (fourierInput observation nontrivial half depth ordinal).1 :=
  (projectionInput observation nontrivial half depth ordinal).2.2.down

theorem fourier_equation : fourierL2 (fourierInput observation nontrivial half depth ordinal).1 =
    (rInput observation nontrivial half depth ordinal).1 :=
  (fourierInput observation nontrivial half depth ordinal).2.2.down

theorem r_equation : burnolDirectRightResolventCLM c (rInput observation nontrivial half depth ordinal).1 =
    (result observation nontrivial half depth ordinal).2.2.1 :=
  (rInput observation nontrivial half depth ordinal).2.2.down

theorem equation : (result observation nontrivial half depth ordinal).2.2.1 =
    burnolDirectRightResolventCLM c (fourierL2 (burnolEvenAmbientProjectionEndomorphism
      (pairedBurnolMultiplicativeDilation shift (Root.waveValue observation nontrivial half depth ordinal)))) := by
  have dilated := (dilation_equation observation nontrivial half depth ordinal).symm.trans
    (congrArg (pairedBurnolMultiplicativeDilation shift)
      (input_binding observation nontrivial half depth ordinal))
  have projected := (projection_equation observation nontrivial half depth ordinal).symm.trans
    (congrArg burnolEvenAmbientProjectionEndomorphism dilated)
  have transformed := (fourier_equation observation nontrivial half depth ordinal).symm.trans
    (congrArg fourierL2 projected)
  exact (r_equation observation nontrivial half depth ordinal).symm.trans
    (congrArg (burnolDirectRightResolventCLM c) transformed)

theorem paid : (result observation nontrivial half depth ordinal).2.1.2.length = 5 :=
  Installed.source_history authority (reader observation nontrivial half depth ordinal) occurrence

end OriginalKPairedWaveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPairedWaveActionSource"
