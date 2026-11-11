import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextPrefixAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKOutsideCorrectionRSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace Action
export OriginalKPaNativeCayleyNextPrefixAction (finalTarget finalOriginFace final_origin_source)
end Action
namespace Root
export OriginalKOutsideCorrectionRootSource
  (rootAdmissions rootSlot rootAdmission correctionValue correctionTrace correctionTrace_heq correction_value)
end Root
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt forcedSourceCode)
end C
namespace Child
export OriginalKOutsideCorrectionChildSource (childCode originalChild)
end Child
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E rCode)
end Prog
namespace Owner
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end Owner
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed
open private decodeMap correctionPath from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

universe u
private theorem mp_heq {α β : Sort u} (same : α = β) (value : α) :
    HEq (Eq.mp same value) value := by
  cases same
  rfl

private theorem get_cast {α : Type} (first second : List α) (same : first = second)
    (index : Fin second.length) :
    first.get (Fin.cast (congrArg List.length same).symm index) = second.get index := by
  cases same
  rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "native" => OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative.native
  observation nontrivial half depth ordinal
local notation "raw" => C.forcedSourceCode observation nontrivial depth half

abbrev sourceRoot := (Action.finalTarget observation nontrivial half depth ordinal).targetRoot
abbrev sourceVisit := (Action.finalTarget observation nontrivial half depth ordinal).targetVisit
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev sourceOccurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (sourceCurrent observation nontrivial half depth ordinal)
local notation "authority" => sourceAuthority observation nontrivial half depth ordinal
local notation "current" => sourceCurrent observation nontrivial half depth ordinal
local notation "occurrence" => sourceOccurrence observation nontrivial half depth ordinal

def finalAdmissions : type_of% (Root.rootAdmissions observation nontrivial half depth ordinal) :=
  (Action.finalOriginFace observation nontrivial half depth ordinal).rootRead.source.occurrences

theorem final_admissions_source : finalAdmissions observation nontrivial half depth ordinal =
    Root.rootAdmissions observation nontrivial half depth ordinal :=
  congrArg (fun payload => payload.source.occurrences)
    (eq_of_heq (Action.final_origin_source observation nontrivial half depth ordinal))

attribute [local irreducible] finalAdmissions

def finalSlot : Fin (finalAdmissions observation nontrivial half depth ordinal).length :=
  Fin.cast (congrArg List.length (final_admissions_source observation nontrivial half depth ordinal)).symm
    (Root.rootSlot observation nontrivial half depth ordinal)

def finalAdmission : type_of% (Root.rootAdmission observation nontrivial half depth ordinal) :=
  (finalAdmissions observation nontrivial half depth ordinal).get
    (finalSlot observation nontrivial half depth ordinal)

theorem final_admission_source : finalAdmission observation nontrivial half depth ordinal =
    Root.rootAdmission observation nontrivial half depth ordinal :=
  get_cast (finalAdmissions observation nontrivial half depth ordinal)
    (Root.rootAdmissions observation nontrivial half depth ordinal)
    (final_admissions_source observation nontrivial half depth ordinal)
    (Root.rootSlot observation nontrivial half depth ordinal)

attribute [local irreducible] physicalValue AS.nativeAfterAdmission

private def readAdmission
    (admitted : type_of% (Root.rootAdmission observation nontrivial half depth ordinal)) : BurnolL2 :=
  physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining raw) correctionPath admitted.1.word)

/-- The final root supplies the literal old forcing word; the existing decoder retains its full correction child. -/
def finalCorrectionValue : BurnolL2 :=
  readAdmission observation nontrivial half depth ordinal
    (finalAdmission observation nontrivial half depth ordinal)

theorem final_correction_source : type_of% (congrArg
    (readAdmission observation nontrivial half depth ordinal)
    (final_admission_source observation nontrivial half depth ordinal)) :=
  congrArg (readAdmission observation nontrivial half depth ordinal)
    (final_admission_source observation nontrivial half depth ordinal)

def finalCorrectionTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1)
    (.const (finalCorrectionValue observation nontrivial half depth ordinal)) :=
  Eq.mp (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1) (.const point))
      (final_correction_source observation nontrivial half depth ordinal).symm)
    (Root.correctionTrace observation nontrivial half depth ordinal)

theorem finalCorrectionTrace_heq : type_of% ((mp_heq (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
      (Child.childCode observation nontrivial half depth 1) (.const point))
        (final_correction_source observation nontrivial half depth ordinal).symm)
      (Root.correctionTrace observation nontrivial half depth ordinal)).trans
    (Root.correctionTrace_heq observation nontrivial half depth ordinal)) :=
  (mp_heq (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
      (Child.childCode observation nontrivial half depth 1) (.const point))
        (final_correction_source observation nontrivial half depth ordinal).symm)
      (Root.correctionTrace observation nontrivial half depth ordinal)).trans
    (Root.correctionTrace_heq observation nontrivial half depth ordinal)

theorem final_correction_value : finalCorrectionValue observation nontrivial half depth ordinal =
    OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c :=
  (final_correction_source observation nontrivial half depth ordinal).trans
    (Root.correction_value observation nontrivial half depth ordinal)

def rEnvironment : Env Prog.Value Prog.Var :=
  fun _ _ => finalCorrectionValue observation nontrivial half depth ordinal

/-- One original R at the already generated final root; its input is the retained root word's child. -/
def rReader {now : (Action.finalTarget observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    Owner.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨rEnvironment observation nontrivial half depth ordinal, Prog.rCode c⟩

def rResult : Installed.ResultAt authority (rReader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (rReader observation nontrivial half depth ordinal) occurrence

private theorem r_expression : (rResult observation nontrivial half depth ordinal).2.1.1 =
    .const ((rResult observation nontrivial half depth ordinal).2.2.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression authority current
    (fun _ => rReader observation nontrivial half depth ordinal occurrence)

def rTrace : Trace (rEnvironment observation nontrivial half depth ordinal) (Prog.rCode c)
    (.const ((rResult observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (rEnvironment observation nontrivial half depth ordinal)
    (Prog.rCode c) expression) (r_expression observation nontrivial half depth ordinal))
    (rResult observation nontrivial half depth ordinal).2.1.2

theorem rTrace_heq : type_of% (mp_heq (congrArg (fun expression => Trace (rEnvironment observation nontrivial half depth ordinal)
      (Prog.rCode c) expression) (r_expression observation nontrivial half depth ordinal))
    (rResult observation nontrivial half depth ordinal).2.1.2) :=
  mp_heq (congrArg (fun expression => Trace (rEnvironment observation nontrivial half depth ordinal)
      (Prog.rCode c) expression) (r_expression observation nontrivial half depth ordinal))
    (rResult observation nontrivial half depth ordinal).2.1.2

def rInput : Σ point : BurnolL2,
    Trace (rEnvironment observation nontrivial half depth ordinal)
      (.var (0 : Fin 2) : Prog.E) (.const point) ×
    PLift (burnolDirectRightResolventCLM c point =
      (rResult observation nontrivial half depth ordinal).2.2.1) :=
  originalInput (rTrace observation nontrivial half depth ordinal)

theorem r_input_binding : (rInput observation nontrivial half depth ordinal).1 =
    finalCorrectionValue observation nontrivial half depth ordinal :=
  (rInput observation nontrivial half depth ordinal).2.1.sound.symm

theorem r_equation : (rResult observation nontrivial half depth ordinal).2.2.1 =
    burnolDirectRightResolventCLM c (finalCorrectionValue observation nontrivial half depth ordinal) :=
  (rInput observation nontrivial half depth ordinal).2.2.down.symm.trans
    (congrArg (burnolDirectRightResolventCLM c) (r_input_binding observation nontrivial half depth ordinal))

theorem r_paid : (rResult observation nontrivial half depth ordinal).2.1.2.length = 2 :=
  Installed.source_history authority (rReader observation nontrivial half depth ordinal) occurrence

/-- A zero read still generates the same two original Steps. -/
theorem r_zero (zero : finalCorrectionValue observation nontrivial half depth ordinal = 0) :
    (rResult observation nontrivial half depth ordinal).2.2.1 = 0 ∧
      (rResult observation nontrivial half depth ordinal).2.1.2.length = 2 :=
  ⟨(r_equation observation nontrivial half depth ordinal).trans
    ((congrArg (burnolDirectRightResolventCLM c) zero).trans (map_zero _)),
    r_paid observation nontrivial half depth ordinal⟩

end OriginalKOutsideCorrectionRSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKOutsideCorrectionRSource"
