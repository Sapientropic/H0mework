import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Semantics

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalRootResidualConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace RM
export ActualCofinalResidualModelSplice
 (semanticZero residual_semantic_zero packetWordTransport packetLanguageWord
  packet_semantic_zero packet_language_semantic_zero semantic_model_equiv)
end RM
namespace CA
export ActualCofinalCommonAction (site projection)
export ActualCofinalCommonAction.T (Factory Frame Programme NativeValue Words Value groups)
end CA
namespace A
export ActualCofinalSourceAction
 (nativePacket selected receipt sourceBorn actual_next_packet packetTransport bornStock born_inventory)
export ActualCofinalSourceAction.AS (AdmissionPacket stockCfg)
end A
namespace C
export ActualCofinalInstalledRaw
 (currentAtStop actual_current requestAtStop materialAtStop materialAtStop_source)
export ActualCanonicalBornSource (MaterialAtCurrent RequestAtCurrent)
end C
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (root visit current)
end SO
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (state presentation compiles_settled birthProgram targetAt target_current)
end ST
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn)
end S
namespace R
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry (query)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt expression)
end N
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace (boundary source_boundary whole_recovery)
end F
namespace T
export ActualNativeRelationTransport (paid)
end T
namespace B
export ActualNativeBornSourceEffect (actual_born_registered_expression)
end B

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (CA.Value W grade target) := CA.groups W grade target

private theorem language_raw_word {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s)) :
 RM.packetLanguageWord same packet (Finsupp.single packet.2.1.1.registered.input.expression 1) =
 Finsupp.single (A.packetTransport same packet).2.1.1.registered.input.expression 1 := by
 cases same
 rfl

private theorem packet_raw_word
 {first second : A.AdmissionPacket (W := W) (X := X) (s := s)} (same : first = second) :
 RM.packetWordTransport same (Finsupp.single first.2.1.1.registered.input.expression 1) =
 Finsupp.single second.2.1.1.registered.input.expression 1 := by cases same; rfl

private theorem packet_current_language {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s)) :
 SO.current (A.packetTransport same packet).2.1.1 (A.packetTransport same packet).2.2.1 =
 SO.current packet.2.1.1 packet.2.2.1 := by cases same; rfl

private theorem material_transport_data
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (material : C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s) first) :
 let actual := Eq.mp
  (congrArg (C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s)) same) material
 actual.environment = material.environment ∧ actual.raw = material.raw ∧
 HEq actual.state material.state ∧ HEq actual.owner material.owner := by
 subst second
 exact ⟨rfl,rfl,HEq.rfl,HEq.rfl⟩

private def requestOfMaterial
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 {current : AnyAuthoritativeRootCurrent.{u}}
 (material : C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s) current) :
 C.RequestAtCurrent (Value := Value) (Var := Var) (s := s) current where
 environment := material.environment
 expression := material.raw
 owner := material.owner

private theorem request_of_material_transport
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (material : C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s) first) :
 requestOfMaterial (Eq.mp
  (congrArg (C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s)) same) material) =
 Eq.mp (congrArg (C.RequestAtCurrent (Value := Value) (Var := Var) (s := s)) same)
  (requestOfMaterial material) := by
 subst second
 rfl

private theorem residual_boundary_semantic
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 {Nw : WorldRelationNetwork.{u}} {Voc : Vocabulary.{u}}
 {lower : SourceNativeLedgerRootClosure Nw Voc} {current : Voc.Current}
 {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
 (material : N.MaterialAt (Value := Value) (Var := Var) (sort := s) occurrence) :
 Finsupp.single (N.expression material) 1 - F.boundary material ∈ RM.semanticZero := by
 rw [F.source_boundary]
 exact RM.residual_semantic_zero material.raw material.state.1

private def birthCurrent
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 (frame : CA.Frame (Value := Value) (Var := Var) (sort := s))
 (configuration : CA.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
 (event : ExactTemporalCausalRootEventAt
  (SO.root frame configuration).toAuthoritativeRoot.toLedgerRoot (SO.visit frame configuration)) :
 AnyAuthoritativeRootCurrent.{u} :=
 let generated := (ST.birthProgram frame configuration).generate event
 ⟨generated.target.TargetN,generated.target.targetAnswerAndNext.nextCurrent⟩

private theorem birth_current
 {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 (frame : CA.Frame (Value := Value) (Var := Var) (sort := s))
 (configuration : CA.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
 (event : ExactTemporalCausalRootEventAt
  (SO.root frame configuration).toAuthoritativeRoot.toLedgerRoot (SO.visit frame configuration)) :
 birthCurrent frame configuration event = SO.current (S.nextBorn frame configuration) configuration :=
 congrArg (fun current => (⟨(ST.targetAt frame configuration event).TargetN,current⟩ : AnyAuthoritativeRootCurrent.{u}))
  (ST.target_current frame configuration event)

variable (factory : CA.Factory W X s)
variable (initial : CA.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : CA.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev source (ordinal : Nat) := CA.site factory initial cfg language ordinal
abbrev native (ordinal : Nat) := A.nativePacket factory (source factory initial cfg language ordinal)
abbrev selected (ordinal : Nat) := A.selected factory (source factory initial cfg language ordinal)
abbrev base (ordinal : Nat) := (native factory initial cfg language ordinal).2.2.1
abbrev installed (ordinal : Nat) := A.stockCfg (base factory initial cfg language ordinal)
abbrev born (ordinal : Nat) := A.sourceBorn factory (source factory initial cfg language ordinal)
abbrev material (ordinal : Nat) := T.paid (selected factory initial cfg language ordinal)

def nextWordTransport (ordinal : Nat) :
 Formal ℤ (CA.Value W (born factory initial cfg language ordinal).1)
  (source factory initial cfg language ordinal).2.2.1.LowVar s →ₗ[ℤ]
 CA.Words factory initial cfg language (ordinal+1) :=
 (RM.packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm).toLinearMap.comp
  (RM.packetLanguageWord (source factory initial cfg language ordinal).2.2.2.down
   (born factory initial cfg language ordinal)).toLinearMap

def boundaryWord (ordinal : Nat) : CA.Words factory initial cfg language (ordinal+1) :=
 nextWordTransport factory initial cfg language ordinal (F.boundary (material factory initial cfg language ordinal))

def residualWord (ordinal : Nat) : CA.Words factory initial cfg language (ordinal+1) :=
 nextWordTransport factory initial cfg language ordinal
  (Finsupp.single (N.expression (material factory initial cfg language ordinal)) 1)

/-- The literal residual is the original next packet's registered AST. -/
theorem residual_word_registered (ordinal : Nat) : residualWord factory initial cfg language ordinal =
 Finsupp.single (source factory initial cfg language (ordinal+1)).2.1.1.registered.input.expression 1 := by
 have sourceAST : (born factory initial cfg language ordinal).2.1.1.registered.input.expression =
  N.expression (material factory initial cfg language ordinal) :=
  B.actual_born_registered_expression (selected factory initial cfg language ordinal) (base factory initial cfg language ordinal)
 change RM.packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm
  (RM.packetLanguageWord (source factory initial cfg language ordinal).2.2.2.down
   (born factory initial cfg language ordinal)
   (Finsupp.single (N.expression (material factory initial cfg language ordinal)) 1)) = _
 rw [←sourceAST,language_raw_word,packet_raw_word]

/-- The whole future fibre is consumed by this original generated request AST. -/
theorem next_model_residual (ordinal : Nat) :
 CA.projection factory initial cfg language
  (DFinsupp.single (ordinal+1) (Finsupp.single (source factory initial cfg language (ordinal+1)).2.1.1.registered.input.expression 1)) =
 CA.projection factory initial cfg language (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal)) := by
 rw [←residual_word_registered]
 apply RM.semantic_model_equiv
 change nextWordTransport factory initial cfg language ordinal
   (Finsupp.single (N.expression (material factory initial cfg language ordinal)) 1) -
  nextWordTransport factory initial cfg language ordinal (F.boundary (material factory initial cfg language ordinal)) ∈ RM.semanticZero
 rw [←map_sub]
 exact RM.packet_semantic_zero _ _
  (RM.packet_language_semantic_zero _ _ _ (residual_boundary_semantic _))

abbrev sourceRoot (ordinal : Nat) := SO.root (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)
abbrev sourceVisit (ordinal : Nat) := SO.visit (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)
abbrev sourceEvent (ordinal : Nat) := (sourceRoot factory initial cfg language ordinal).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (sourceVisit factory initial cfg language ordinal)
def generated (ordinal : Nat) :=
 (ST.birthProgram (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)).generate
  (sourceEvent factory initial cfg language ordinal)

def generatedCurrent (ordinal : Nat) : AnyAuthoritativeRootCurrent.{u} :=
 birthCurrent (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)
  (sourceEvent factory initial cfg language ordinal)

/-- The source receipt drives the original compiler's settled consumer. -/
theorem original_compiles (ordinal : Nat) :
 (ST.state (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)).compileInquiry
  (R.query (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)) =
 .debtAdmission (generated factory initial cfg language ordinal) :=
 ST.compiles_settled _ _ (A.receipt factory (source factory initial cfg language ordinal)).2.1
  (A.receipt factory (source factory initial cfg language ordinal)).2.2.2

/-- The generated whole-next current is the original actual next admission current. -/
theorem actual_generated_current (ordinal : Nat) : C.currentAtStop factory initial cfg language (ordinal+1) =
 generatedCurrent factory initial cfg language ordinal := by
 have rootNext : generatedCurrent factory initial cfg language ordinal =
  SO.current (born factory initial cfg language ordinal).2.1.1 (born factory initial cfg language ordinal).2.2.1 :=
  birth_current (selected factory initial cfg language ordinal) (installed factory initial cfg language ordinal)
   (sourceEvent factory initial cfg language ordinal)
 exact (C.actual_current factory initial cfg language (ordinal+1)).trans
  ((congrArg (fun packet => SO.current packet.2.1.1 packet.2.2.1)
    (A.actual_next_packet factory initial cfg language ordinal)).trans
   ((packet_current_language (source factory initial cfg language ordinal).2.2.2.down
     (born factory initial cfg language ordinal)).trans rootNext.symm))

/-- The complete material retains the next source's trace and responsibility owner. -/
def rootedMaterial (ordinal : Nat) : C.MaterialAtCurrent
 (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s)
 (generatedCurrent factory initial cfg language ordinal) :=
 Eq.mp (congrArg (C.MaterialAtCurrent
  (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s))
  (actual_generated_current factory initial cfg language ordinal))
  (C.materialAtStop factory initial cfg language (ordinal+1))

theorem rooted_material_source (ordinal : Nat) :
 (rootedMaterial factory initial cfg language ordinal).environment =
  (source factory initial cfg language (ordinal+1)).2.1.1.registered.input.environment ∧
 (rootedMaterial factory initial cfg language ordinal).raw =
  (source factory initial cfg language (ordinal+1)).2.1.1.registered.input.expression ∧
 HEq (rootedMaterial factory initial cfg language ordinal).state
  (source factory initial cfg language (ordinal+1)).2.1.1.event.state ∧
 HEq (rootedMaterial factory initial cfg language ordinal).owner
  (T.paid (source factory initial cfg language (ordinal+1)).2.1.1).owner := by
 have carried := material_transport_data _ _
  (actual_generated_current factory initial cfg language ordinal)
  (C.materialAtStop factory initial cfg language (ordinal+1))
 have actual := C.materialAtStop_source factory initial cfg language (ordinal+1)
 exact ⟨carried.1.trans actual.1,carried.2.1.trans actual.2.1,
  carried.2.2.1.trans actual.2.2.1,carried.2.2.2.trans actual.2.2.2⟩

/-- The writable Raw/Env/owner come from the original canonical next source. -/
def rootedRequest (ordinal : Nat) : C.RequestAtCurrent
 (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s)
 (generatedCurrent factory initial cfg language ordinal) :=
 requestOfMaterial (rootedMaterial factory initial cfg language ordinal)

theorem rooted_request_transport (ordinal : Nat) :
 rootedRequest factory initial cfg language ordinal =
 Eq.mp (congrArg (C.RequestAtCurrent
  (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s))
  (actual_generated_current factory initial cfg language ordinal))
  (C.requestAtStop factory initial cfg language (ordinal+1)) :=
 request_of_material_transport _ _ (actual_generated_current factory initial cfg language ordinal)
  (C.materialAtStop factory initial cfg language (ordinal+1))

theorem rooted_request_source (ordinal : Nat) :
 (rootedRequest factory initial cfg language ordinal).environment =
  (rootedMaterial factory initial cfg language ordinal).environment ∧
 (rootedRequest factory initial cfg language ordinal).expression =
  (rootedMaterial factory initial cfg language ordinal).raw ∧
 HEq (rootedRequest factory initial cfg language ordinal).owner
  (rootedMaterial factory initial cfg language ordinal).owner :=
 ⟨rfl,rfl,HEq.rfl⟩

/-- The original next responsibility's executable input represents this complete Model residual. -/
theorem rooted_request_model (ordinal : Nat) :
 CA.projection factory initial cfg language
  (DFinsupp.single (ordinal+1) (Finsupp.single (rootedRequest factory initial cfg language ordinal).expression 1)) =
 CA.projection factory initial cfg language (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal)) := by
 have raw : (rootedRequest factory initial cfg language ordinal).expression =
   (source factory initial cfg language (ordinal+1)).2.1.1.registered.input.expression :=
  (rooted_material_source factory initial cfg language ordinal).2.1
 rw [raw]
 exact next_model_residual factory initial cfg language ordinal

/-- The original whole-ledger first destination remains the source of this certified request. -/
theorem original_whole (ordinal : Nat) : type_of%
 (generated factory initial cfg language ordinal).target.firstDestination_heq :=
 (generated factory initial cfg language ordinal).target.firstDestination_heq

/-- The original selected responsibility is evolved by the actual whole first write. -/
def originalOldRow (ordinal : Nat) :=
 let target := (generated factory initial cfg language ordinal).target
 target.firstSuccessor.ledgerEvolution.destination
  (target.initialSupport_eq.symm ▸
   DebtActivationWorld.oldEntry (law := target.law) (state? := some target.sourceState)
    ((selected factory initial cfg language ordinal).currentState.entryAt PUnit.unit))

/-- The same whole write supplies the born responsibility and its paid evolution. -/
def originalBornRow (ordinal : Nat) :=
 let target := (generated factory initial cfg language ordinal).target
 target.firstSuccessor.ledgerEvolution.destination
  (target.initialSupport_eq.symm ▸
   DebtActivationWorld.debtEntry
    ((sourceRoot factory initial cfg language ordinal).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
     (sourceEvent factory initial cfg language ordinal).occurrence) target.sourceState)

def consume (ordinal : Nat) :
 Σ request : C.RequestAtCurrent
  (Value := CA.NativeValue factory initial cfg language (ordinal+1)) (Var := X) (s := s)
  (generatedCurrent factory initial cfg language ordinal),
 PLift (CA.projection factory initial cfg language
  (DFinsupp.single (ordinal+1) (Finsupp.single request.expression 1)) =
  CA.projection factory initial cfg language (DFinsupp.single (ordinal+1) (boundaryWord factory initial cfg language ordinal))) ×
 PLift (type_of% (original_compiles factory initial cfg language ordinal)) ×
 PLift (type_of% (original_whole factory initial cfg language ordinal)) :=
 ⟨rootedRequest factory initial cfg language ordinal,⟨rooted_request_model factory initial cfg language ordinal⟩,
  ⟨original_compiles factory initial cfg language ordinal⟩,⟨original_whole factory initial cfg language ordinal⟩⟩

end ActualCofinalRootResidualConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
