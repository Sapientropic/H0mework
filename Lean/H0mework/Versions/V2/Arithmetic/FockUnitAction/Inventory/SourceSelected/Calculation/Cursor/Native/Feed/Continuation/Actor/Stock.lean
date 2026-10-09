import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Stock
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActuality
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirect
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
  (F.dynamicFeed F.Values F.Vars C.continuous pointEnv initial_env)
end S
namespace C
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Source (Frame environmentAt)
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Consumer (born_source_action)
end C
namespace Old
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Consumer
  (rawCoimage rawMaterial raw_full raw_material raw_prefix raw_completed raw_original_disposition nativeBudget
   R.calculatedValue R.actor R.runtime R.Point K.someLift)
end Old
namespace N
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
  (recover cursorRestriction)
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action (actualAction)
end N
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (runtime frames next nextBorn datum actualOccurrence resultFace)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment
  (At active epoch mathNext frames_constant born_constant born_raw)
end E
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme lowResult decoder_preserved)
end I
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_environment)
end P
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births
  (birthIndex startIndex startIndex_succ actual_action)
end B
namespace K
export SourceOperationInquiry.Context.Native.Frame.Stock (frameAt frame_actual)
end K
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (rawSource environment_actual)
end O

private theorem decoded_same {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    (frame : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort))
    (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (reader : {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} →
      SourceOperationInquiry.Context.Installation.Occurrence frame (current := current) → PairValue Value sort → Env Value Var)
    (reads : (A.datum frame configuration).nextEnvironmentReadAt = some @reader) :
    (A.epoch (A.nextBorn frame (I.programme configuration))).activeEnvironment =
      (A.epoch (A.nextBorn frame configuration)).activeEnvironment := by
  let wrappedReader : {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (A.epoch frame).registered} →
      SourceOperationInquiry.Context.Installation.Occurrence (A.epoch frame) (current := current) →
        PairValue Value sort → Env Value Var := fun {current} supplied _ => @reader current supplied
          (I.lowResult (A.epoch frame) configuration supplied).2.2.1
  have wrapped : (A.datum frame (I.programme configuration)).nextEnvironmentReadAt = some @wrappedReader := by
    dsimp only [A.datum] at reads
    simp only [A.datum, I.programme, reads, wrappedReader]
  have low : (A.epoch (A.nextBorn frame configuration)).activeEnvironment =
      reader (A.actualOccurrence frame) (I.lowResult (A.epoch frame) configuration (A.actualOccurrence frame)).2.2.1 := by
    change (match (A.datum frame configuration).nextEnvironmentReadAt with
      | some read => read (A.actualOccurrence frame) ((A.resultFace frame configuration).rootRead.2.2.1)
      | none => _) = _
    rw [reads]
    rfl
  have decoded := I.decoder_preserved frame configuration
    ((A.resultFace frame (I.programme configuration)).rootRead.2.2.1)
  rw [reads, wrapped] at decoded
  have next : (A.epoch (A.nextBorn frame (I.programme configuration))).activeEnvironment =
      reader (A.actualOccurrence frame) (I.lowResult (A.epoch frame) configuration (A.actualOccurrence frame)).2.2.1 := by
    change (match (A.datum frame (I.programme configuration)).nextEnvironmentReadAt with
      | some read => read (A.actualOccurrence frame) ((A.resultFace frame (I.programme configuration)).rootRead.2.2.1)
      | none => _) = _
    rw [wrapped]
  exact next.trans ((Option.some.inj decoded).trans low.symm)

theorem actor_decoder (depth count stage : Nat) :
    (A.epoch (A.nextBorn (K.frameAt (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage)
      (I.programme (S.C.continuous depth count)))).activeEnvironment false Unit.unit =
    N.actualAction depth count
      ((A.epoch (K.frameAt (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage)).activeEnvironment false Unit.unit) := by
  let frame := K.frameAt (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage
  have same := decoded_same frame (S.C.continuous depth count)
    (fun {_current} _occurrence value => C.environmentAt depth count (A.epoch frame).activeEnvironment (value.1 + value.2).1) rfl
  exact (congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit) same).trans
    (C.born_source_action depth count frame)

abbrev low (depth count : Nat) := S.C.continuous depth count
abbrev stock (depth count : Nat) := I.programme (low depth count)
abbrev frameAt (depth count stage : Nat) := A.frames (S.F.dynamicFeed depth count) (stock depth count) stage
abbrev lowFrameAt (depth count stage : Nat) := A.frames (S.F.dynamicFeed depth count) (low depth count) stage
abbrev birth (depth count ordinal : Nat) := B.birthIndex (stock depth count) (S.F.dynamicFeed depth count) ordinal
abbrev lowBirth (depth count ordinal : Nat) := B.birthIndex (low depth count) (S.F.dynamicFeed depth count) ordinal

theorem stock_constant (depth count stage : Nat) :
    E.At (frameAt depth count stage) (frameAt depth count stage).activeEnvironment :=
  E.frames_constant (stock depth count) (S.initial_env depth count) stage
theorem low_constant (depth count stage : Nat) :
    E.At (lowFrameAt depth count stage) (lowFrameAt depth count stage).activeEnvironment :=
  E.frames_constant (low depth count) (S.initial_env depth count) stage

private theorem active_born (depth count : Nat)
    (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
      (PhysicalValue := S.F.Values depth count) (PhysicalVar := S.F.Vars) (sort := true))
    (frame : C.Frame depth count) (uniform : E.At frame frame.activeEnvironment)
    (source : (A.epoch (A.nextBorn frame configuration)).activeEnvironment false Unit.unit =
      N.actualAction depth count ((A.epoch frame).activeEnvironment false Unit.unit)) :
    (A.nextBorn frame configuration).activeEnvironment false Unit.unit =
      N.actualAction depth count (frame.activeEnvironment false Unit.unit) := by
  have born : E.At (A.nextBorn frame configuration) (A.nextBorn frame configuration).activeEnvironment :=
    E.born_constant configuration uniform
  exact (congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit) (E.epoch born)).symm.trans
    (source.trans (congrArg (N.actualAction depth count)
      (congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit) (E.epoch uniform))))

theorem stock_born_action (depth count stage : Nat) :
    (A.nextBorn (frameAt depth count stage) (stock depth count)).activeEnvironment false Unit.unit =
      N.actualAction depth count ((frameAt depth count stage).activeEnvironment false Unit.unit) := by
  let claim (frame : C.Frame depth count) : Prop :=
    (A.epoch (A.nextBorn frame (stock depth count))).activeEnvironment false Unit.unit =
      N.actualAction depth count ((A.epoch frame).activeEnvironment false Unit.unit)
  have source : claim (K.frameAt (S.F.dynamicFeed depth count) (low depth count) stage) :=
    actor_decoder depth count stage
  have actual := Eq.mp (congrArg claim (K.frame_actual (S.F.dynamicFeed depth count) (low depth count) stage)) source
  exact active_born depth count (stock depth count) _ (stock_constant depth count stage) actual
theorem low_born_action (depth count stage : Nat) :
    (A.nextBorn (lowFrameAt depth count stage) (low depth count)).activeEnvironment false Unit.unit =
      N.actualAction depth count ((lowFrameAt depth count stage).activeEnvironment false Unit.unit) :=
  active_born depth count (low depth count) _ (low_constant depth count stage)
    (C.born_source_action depth count (lowFrameAt depth count stage))

theorem stock_after_birth (depth count ordinal : Nat) :
    frameAt depth count (birth depth count ordinal + 1) =
      A.nextBorn (frameAt depth count (birth depth count ordinal)) (stock depth count) := by
  change A.next _ _ = _
  unfold A.next
  rw [B.actual_action (stock depth count) (S.F.dynamicFeed depth count) ordinal]
theorem low_after_birth (depth count ordinal : Nat) :
    lowFrameAt depth count (lowBirth depth count ordinal + 1) =
      A.nextBorn (lowFrameAt depth count (lowBirth depth count ordinal)) (low depth count) := by
  change A.next _ _ = _
  unfold A.next
  rw [B.actual_action (low depth count) (S.F.dynamicFeed depth count) ordinal]

theorem stock_at_start (depth count ordinal : Nat) :
    (frameAt depth count (birth depth count ordinal)).activeEnvironment =
      (frameAt depth count (B.startIndex (stock depth count) (S.F.dynamicFeed depth count) ordinal)).activeEnvironment :=
  P.receipt_environment (stock depth count) (S.F.dynamicFeed depth count) (S.initial_env depth count) _
theorem low_at_start (depth count ordinal : Nat) :
    (lowFrameAt depth count (lowBirth depth count ordinal)).activeEnvironment =
      (lowFrameAt depth count (B.startIndex (low depth count) (S.F.dynamicFeed depth count) ordinal)).activeEnvironment :=
  P.receipt_environment (low depth count) (S.F.dynamicFeed depth count) (S.initial_env depth count) _

theorem birth_field_same (depth count ordinal : Nat) :
    (frameAt depth count (birth depth count ordinal)).activeEnvironment false Unit.unit =
      (lowFrameAt depth count (lowBirth depth count ordinal)).activeEnvironment false Unit.unit := by
  induction ordinal with
  | zero =>
      have newSource := stock_at_start depth count 0
      have oldSource := low_at_start depth count 0
      exact congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit)
        (newSource.trans oldSource.symm)
  | succ ordinal previous =>
      have newSource := congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit)
        (stock_at_start depth count (ordinal + 1))
      have oldSource := congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit)
        (low_at_start depth count (ordinal + 1))
      change (frameAt depth count (birth depth count (ordinal + 1))).activeEnvironment false Unit.unit =
        (frameAt depth count (birth depth count ordinal + 1)).activeEnvironment false Unit.unit at newSource
      change (lowFrameAt depth count (lowBirth depth count (ordinal + 1))).activeEnvironment false Unit.unit =
        (lowFrameAt depth count (lowBirth depth count ordinal + 1)).activeEnvironment false Unit.unit at oldSource
      have newBorn := (congrArg (fun frame : C.Frame depth count => frame.activeEnvironment false Unit.unit)
        (stock_after_birth depth count ordinal)).trans (stock_born_action depth count (birth depth count ordinal))
      have oldBorn := (congrArg (fun frame : C.Frame depth count => frame.activeEnvironment false Unit.unit)
        (low_after_birth depth count ordinal)).trans (low_born_action depth count (lowBirth depth count ordinal))
      exact newSource.trans (newBorn.trans ((congrArg (N.actualAction depth count) previous).trans
        (oldBorn.symm.trans oldSource.symm)))

abbrev runtime (depth count : Nat) := A.runtime (S.F.dynamicFeed depth count) (stock depth count)
def rawCoimage (depth count ordinal : Nat) : S.F.Values depth count false :=
  (SourceOperationInquiry.Context.readEnv (runtime depth count)
    (O.rawSource (S.F.dynamicFeed depth count) (stock depth count))
    ((runtime depth count).stateAt (birth depth count ordinal + 1))) false Unit.unit
def rawMaterial (depth count ordinal : Nat) :=
  N.cursorRestriction depth (N.recover depth count (rawCoimage depth count ordinal))

theorem raw_coimage_same (depth count ordinal : Nat) : rawCoimage depth count ordinal = Old.rawCoimage depth count ordinal := by
  rw [rawCoimage, Old.rawCoimage, O.environment_actual, O.environment_actual]
  have newRaw := congrArg (fun frame : C.Frame depth count => frame.rawRead.environment false Unit.unit)
    (stock_after_birth depth count ordinal)
  have oldRaw := congrArg (fun frame : C.Frame depth count => frame.rawRead.environment false Unit.unit)
    (low_after_birth depth count ordinal)
  have newBorn := congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit)
    (E.born_raw (stock depth count) (frameAt depth count (birth depth count ordinal)))
  have oldBorn := congrArg (fun env : Env (S.F.Values depth count) S.F.Vars => env false Unit.unit)
    (E.born_raw (low depth count) (lowFrameAt depth count (lowBirth depth count ordinal)))
  exact newRaw.trans (newBorn.trans ((birth_field_same depth count ordinal).trans (oldBorn.symm.trans oldRaw.symm)))
theorem raw_material_same (depth count ordinal : Nat) : rawMaterial depth count ordinal = Old.rawMaterial depth count ordinal :=
  congrArg (fun value => N.cursorRestriction depth (N.recover depth count value)) (raw_coimage_same depth count ordinal)
theorem full_original_word (depth count ordinal : Nat) : type_of%
    ((congrArg (N.recover depth count) (raw_coimage_same depth count ordinal)).trans (Old.raw_full depth count ordinal)) :=
  (congrArg (N.recover depth count) (raw_coimage_same depth count ordinal)).trans (Old.raw_full depth count ordinal)
theorem original_material (depth count ordinal : Nat) : type_of%
    ((raw_material_same depth count ordinal).trans (Old.raw_material depth count ordinal)) :=
  (raw_material_same depth count ordinal).trans (Old.raw_material depth count ordinal)
theorem original_completed (depth count : Nat) :
    rawMaterial depth count (Old.nativeBudget depth) = Old.K.someLift depth (Old.R.calculatedValue depth) :=
  (raw_material_same depth count (Old.nativeBudget depth)).trans (Old.raw_completed depth count)

theorem original_disposition (depth count : Nat) :
    (∃ reached : ReachedAt (Old.R.actor depth).rooted.rootSource.source,
      rawMaterial depth count (Old.nativeBudget depth) = Old.K.someLift depth (Finsupp.single
        (⟨(Old.R.runtime depth).emittedOccurrence, .completed (.inl reached)⟩ : Old.R.Point depth) 1) ∧
      ∃ generated : PrimePairActualitySettlementAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .settlement generated) ∨
    (∃ exhausted : ExhaustedAt (Old.R.actor depth).rooted.rootSource.source,
      rawMaterial depth count (Old.nativeBudget depth) = Old.K.someLift depth (Finsupp.single
        (⟨(Old.R.runtime depth).emittedOccurrence, .completed (.inr exhausted)⟩ : Old.R.Point depth) 1) ∧
      ∃ generated : PrimePairActualityObstructionAt (directRuntimeActuality depth),
        generatePrimePairActualityDisposition (directRuntimeActuality depth) = .obstruction generated) := by
  have material := raw_material_same depth count (Old.nativeBudget depth)
  rcases Old.raw_original_disposition depth count with
    ⟨reached, observed, generated, actual⟩ | ⟨exhausted, observed, generated, actual⟩
  · exact .inl ⟨reached, material.trans observed, generated, actual⟩
  · exact .inr ⟨exhausted, material.trans observed, generated, actual⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Stock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
