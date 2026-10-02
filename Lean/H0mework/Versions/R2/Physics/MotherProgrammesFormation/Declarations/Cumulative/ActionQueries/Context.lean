import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Restriction
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.World
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

abbrev Context := Σ network : WorldRelationNetwork.{0},
  Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure network vocabulary

def contextOfCurrent (world : Σ network : WorldRelationNetwork.{0}, SourceNativeLivingRootCurrentAt network) : Context :=
  ⟨world.1, world.2.V, world.2.root⟩

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {old : SourceNativeLivingRootCurrentAt N}
    {materials : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank}

/-- Network, vocabulary and living root are all actual value readouts. -/
def context (p : MotherNativeCurrent.Restriction rank old materials) : Context :=
  contextOfCurrent (MotherNativeCurrent.world p.presentation.authority.network p.read)

theorem context_eq (p : MotherNativeCurrent.Restriction rank old materials) : context p = ⟨N, old.V, old.root⟩ := by
  unfold context
  rw [p.read_eq, MotherNativeCurrent.world_eq]
  rfl

def networkCoordinates (p : MotherNativeCurrent.Restriction rank old materials) :
    MotherActionTranslation.Coordinates (rank := rank) N :=
  MotherActionTranslation.coordinatesOfRoot (MotherArenaHigher.split rank materials.1).1 p.value.1
    (MotherHandoffSource.joint_root_formed materials.1 p.value p.formed) p.presentation.authority

def occurrenceCoordinates (p : MotherNativeCurrent.Restriction rank old materials) (current : old.V.Current) :
    old.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank :=
  MotherAuthorityCoordinates.occurrence (MotherArenaHigher.split rank materials.1).1 p.value.1
    (MotherHandoffSource.joint_root_formed materials.1 p.value p.formed) p.presentation.authority current

variable {V : ConstructiveRoot.Vocabulary.{0}} {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit event entry authority

abbrev BodyAt (world : Context) := MotherActionBody.Body
  (root := root) (visit := visit) (event := event) (entry := entry) world.2.2

structure ContextCoordinates (lower : Ordinal.{0}) (world : Context) where
  network : MotherActionTranslation.Coordinates (rank := lower) world.1
  occurrence : MotherActionBody.TargetOccurrence world.2.2 ↪ MotherArenaHigher.Base lower

/-- The body compiler runs on the actual restored heterogeneous root.
Only its resulting dependent type is restricted to the inverse schema. -/
def formBodyAtContext {before : Context} (after : Context) (same : after = before)
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := rank) N)
    (oldOccurrence : MotherActionBody.SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base rank)
    (schema : ContextCoordinates rank before) (material : MotherArenaHigher.Material rank) :
    Option (BodyAt (root := root) (visit := visit) (event := event) (entry := entry) before) :=
  let actualSchema := Eq.mp (congrArg (ContextCoordinates rank) same.symm) schema
  (MotherActionBody.form (event := event) (entry := entry) after.2.2 oldCoordinates actualSchema.network
    oldOccurrence actualSchema.occurrence material).map
      (Eq.mp (congrArg (BodyAt (root := root) (visit := visit) (event := event) (entry := entry)) same))

theorem formBodyAtContext_eq {before : Context} (after : Context) (same : after = before)
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := rank) N)
    (oldOccurrence : MotherActionBody.SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base rank)
    (schema : ContextCoordinates rank before) (material : MotherArenaHigher.Material rank) :
    formBodyAtContext (event := event) (entry := entry) after same oldCoordinates oldOccurrence schema material =
      MotherActionBody.form (event := event) (entry := entry) before.2.2 oldCoordinates schema.network oldOccurrence schema.occurrence material := by
  cases same
  unfold formBodyAtContext
  change Option.map id _ = _
  simp only [Option.map_id]
  rfl

/-- Full target fields are installed over the actual heterogeneous target
context. The old context is only the inverse dependency schema. -/
def assembleContext (target : Target) (world : Context)
    (same : world = ⟨target.TargetN, target.TargetV, target.targetRoot⟩)
    (body : MotherActionBody.Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (selected : Sigma target.Receipt) : Target :=
  MotherActionBody.assemble (targetRoot := world.2.2)
    (Eq.mp (congrArg (BodyAt (root := root) (visit := visit) (event := event) (entry := entry)) same.symm) body)
    target.Answer target.Receipt selected

theorem assembleContext_network (target : Target) (world : Context)
    (same : world = ⟨target.TargetN, target.TargetV, target.targetRoot⟩)
    (body : MotherActionBody.Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (selected : Sigma target.Receipt) :
    (assembleContext target world same body selected).TargetN = world.1 := rfl

theorem assembleContext_root (target : Target) (world : Context)
    (same : world = ⟨target.TargetN, target.TargetV, target.targetRoot⟩)
    (body : MotherActionBody.Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (selected : Sigma target.Receipt) :
    (assembleContext target world same body selected).targetRoot = world.2.2 := rfl

theorem assembleContext_recovers (target : Target) (world : Context)
    (same : world = ⟨target.TargetN, target.TargetV, target.targetRoot⟩)
    (body : MotherActionBody.Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (bodySame : body = MotherActionBody.ofTarget target) {upper : Ordinal.{3}}
    {value : MotherReceiptPayload.Value upper}
    (receipt : MotherReceiptPayload.Presentation target.Answer target.Receipt ⟨target.answer, target.receipt⟩ value) :
    assembleContext target world same body receipt.restrict = target := by
  cases same
  exact MotherActionBody.target_recovers target body bodySame receipt

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
