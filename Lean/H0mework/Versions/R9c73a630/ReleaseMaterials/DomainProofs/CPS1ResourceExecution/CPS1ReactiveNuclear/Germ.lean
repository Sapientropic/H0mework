import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveNuclear.Birth
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Current

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveNuclear
noncomputable section
open CPS1ElectronicSource
open CPS1ReactiveField CPS1ReactiveField.Carried
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

abbrev Birth.Id (birth : Birth root state) := {key : Key root // key ∈ birth.nuclearKeys}

instance (birth : Birth root state) : DecidableEq birth.Id := inferInstance

instance (birth : Birth root state) : Fintype birth.Id :=
  Fintype.subtype birth.nuclearKeys.toFinset (fun _ => List.mem_toFinset)

/-- The equivalence is the finite readout of this actual list, generated only
from its source keys. It is never supplied to a physical entry point. -/
def Birth.slotEquiv (birth : Birth root state) (unique : birth.nuclearKeys.Nodup) :
    Fin state.nuclei.length ≃ birth.Id :=
  (finCongr birth.nuclearLength.symm).trans (List.Nodup.getEquiv birth.nuclearKeys unique)

def Birth.nuclearId (birth : Birth root state) (unique : birth.nuclearKeys.Nodup)
    (slot : Fin state.nuclei.length) : birth.Id := birth.slotEquiv unique slot

def Birth.node (birth : Birth root state) (unique : birth.nuclearKeys.Nodup)
    (id : birth.Id) : CPS1AtomicDynamics.Body.Node :=
  state.nuclei.get ((birth.slotEquiv unique).symm id)

def Birth.primitiveId (birth : Birth root state)
    (covered : ∀ primitive, birth.primitiveKey primitive ∈ birth.nuclearKeys)
    (primitive : state.PrimitiveIndex) : birth.Id := ⟨birth.primitiveKey primitive,covered primitive⟩

theorem Birth.node_nuclearId (birth : Birth root state) (unique : birth.nuclearKeys.Nodup)
    (slot : Fin state.nuclei.length) :
    birth.node unique (birth.nuclearId unique slot) = state.nuclei.get slot := by
  simp only [Birth.node,Birth.nuclearId,Equiv.symm_apply_apply]

/-- An admitted germ contains source-produced identities and exact stored
centres. It does not contain a Hamiltonian, caller basis or target update. -/
structure Germ (root : CPS1Deformation.Source.Occurrence frame) (state : Snapshot) where
  birth : Birth root state
  unique : birth.nuclearKeys.Nodup
  covered : ∀ primitive, birth.primitiveKey primitive ∈ birth.nuclearKeys
  centre : ∀ primitive, (state.primitive primitive).centre =
    Geometry.nucleusPosition (birth.node unique (birth.primitiveId covered primitive))
  positive : ∀ id : birth.Id, 0 < (birth.node unique id).row.inertia
  ready : CPS1AtomicDynamics.Body.ready state.nuclei

inductive GermFailure
  | identity (failure : IdentityFailure)
  | duplicateNuclearIdentity
  | missingPrimitiveNucleus
  | inconsistentPrimitiveCentre
  | nonpositiveNuclearInertia
  | collision
  deriving DecidableEq

/-- Every recognition obligation is paid inside the source producer. A
rejection retains the complete existing Snapshot in its surrounding current. -/
def admitBirth (birth : Birth root state) : Except GermFailure (Germ root state) := by
  classical
  exact if unique : birth.nuclearKeys.Nodup then
    if covered : ∀ primitive, birth.primitiveKey primitive ∈ birth.nuclearKeys then
      if centre : ∀ primitive, (state.primitive primitive).centre =
          Geometry.nucleusPosition (birth.node unique (birth.primitiveId covered primitive)) then
        if positive : ∀ id : birth.Id, 0 < (birth.node unique id).row.inertia then
          if ready : CPS1AtomicDynamics.Body.ready state.nuclei then
            .ok ⟨birth,unique,covered,centre,positive,ready⟩
          else .error .collision
        else .error .nonpositiveNuclearInertia
      else .error .inconsistentPrimitiveCentre
    else .error .missingPrimitiveNucleus
  else .error .duplicateNuclearIdentity

abbrev Germ.Id (germ : Germ root state) := germ.birth.Id
abbrev Germ.Configuration (germ : Germ root state) := germ.Id → Point
abbrev Germ.Coefficients (_germ : Germ root state) := Matrix state.PrimitiveIndex state.ElectronIndex ℂ
abbrev Germ.FullConfiguration (germ : Germ root state) :=
  (germ.Configuration × germ.Configuration) × germ.Coefficients

def Germ.primitiveId (germ : Germ root state) (primitive : state.PrimitiveIndex) : germ.Id :=
  germ.birth.primitiveId germ.covered primitive

def Germ.nuclearId (germ : Germ root state) (slot : Fin state.nuclei.length) : germ.Id :=
  germ.birth.nuclearId germ.unique slot

def Germ.node (germ : Germ root state) (id : germ.Id) : CPS1AtomicDynamics.Body.Node :=
  germ.birth.node germ.unique id

def Germ.positions (germ : Germ root state) : germ.Configuration :=
  fun id => Geometry.nucleusPosition (germ.node id)
def Germ.momenta (germ : Germ root state) : germ.Configuration :=
  fun id axis => (germ.node id).row.momentum axis

def Germ.current (germ : Germ root state) : germ.FullConfiguration :=
  ((germ.positions,germ.momenta),state.occupied)

def Germ.primitiveAt (germ : Germ root state) (positions : germ.Configuration)
    (index : state.PrimitiveIndex) : Primitive :=
  {state.primitive index with centre := positions (germ.primitiveId index)}

def Germ.nodeAt (germ : Germ root state) (positions momenta : germ.Configuration)
    (slot : Fin state.nuclei.length) : CPS1AtomicDynamics.Body.Node :=
  {state.nuclei.get slot with row :=
    {(state.nuclei.get slot).row with
      position := euclideanPoint (positions (germ.nuclearId slot))
      momentum := euclideanPoint (momenta (germ.nuclearId slot))}}

def Germ.snapshotAt (germ : Germ root state) (configuration : germ.FullConfiguration) : Snapshot :=
  {state with
    primitive := germ.primitiveAt configuration.1.1
    occupied := configuration.2
    nuclei := List.ofFn (germ.nodeAt configuration.1.1 configuration.1.2)}

def Germ.energy (germ : Germ root state) (configuration : germ.FullConfiguration) : ℝ :=
  (germ.snapshotAt configuration).energy

def Germ.nuclearEnergy (germ : Germ root state)
    (positions momenta : germ.Configuration) : ℝ :=
  CPS1AtomicDynamics.Body.energy (List.ofFn (germ.nodeAt positions momenta))

theorem Germ.primitive_current (germ : Germ root state) (index : state.PrimitiveIndex) :
    germ.primitiveAt germ.positions index = state.primitive index := by
  unfold Germ.primitiveAt Germ.positions Germ.node Germ.primitiveId
  rw [← germ.centre index]

theorem Germ.node_current (germ : Germ root state) (slot : Fin state.nuclei.length) :
    germ.nodeAt germ.positions germ.momenta slot = state.nuclei.get slot := by
  have original : germ.node (germ.nuclearId slot) = state.nuclei.get slot :=
    germ.birth.node_nuclearId germ.unique slot
  have position : euclideanPoint (germ.positions (germ.nuclearId slot)) =
      (state.nuclei.get slot).row.position := by
    apply WithLp.ofLp_injective
    funext axis
    change (germ.node (germ.nuclearId slot)).row.position axis = _
    rw [original]
  have momentum : euclideanPoint (germ.momenta (germ.nuclearId slot)) =
      (state.nuclei.get slot).row.momentum := by
    apply WithLp.ofLp_injective
    funext axis
    change (germ.node (germ.nuclearId slot)).row.momentum axis = _
    rw [original]
  simp only [Germ.nodeAt,position,momentum]

theorem Germ.snapshot_current (germ : Germ root state) : germ.snapshotAt germ.current = state := by
  have primitive : germ.primitiveAt germ.positions = state.primitive := funext germ.primitive_current
  have nuclear : List.ofFn (germ.nodeAt germ.positions germ.momenta) = state.nuclei := by
    rw [show germ.nodeAt germ.positions germ.momenta = state.nuclei.get from funext germ.node_current]
    exact List.ofFn_get _
  simp only [Germ.snapshotAt,Germ.current,primitive,nuclear]

theorem Germ.jet_current (germ : Germ root state) (electron : state.ElectronIndex) (jet : Fin 3 → Nat) :
    (germ.snapshotAt germ.current).jet electron jet = state.jet electron jet := by
  change (∑ primitive, state.occupied primitive electron •
    (germ.primitiveAt germ.positions primitive).jet jet) = state.jet electron jet
  simp only [Germ.primitive_current,Snapshot.jet]

theorem Germ.current_square (germ : Germ root state) :
    germ.snapshotAt germ.current = state ∧
    (∀ electron : state.ElectronIndex, ∀ jet,
      (germ.snapshotAt germ.current).jet electron jet = state.jet electron jet) ∧
    (germ.snapshotAt germ.current).fields = state.fields ∧
    (germ.snapshotAt germ.current).nuclei = state.nuclei ∧
    germ.energy germ.current = state.energy ∧
    (germ.snapshotAt germ.current).account = state.account := by
  refine ⟨germ.snapshot_current,germ.jet_current,?_,
    congrArg Snapshot.nuclei germ.snapshot_current,
    congrArg Snapshot.energy germ.snapshot_current,
    congrArg Snapshot.account germ.snapshot_current⟩
  funext electron
  exact germ.jet_current electron 0

/-- This initial constructor consumes the actual existing Material. Its final
raw-source entry will call it internally after the original native producer. -/
def initialGerm {current : Occurrence frame} (material : Material current) :
    Except GermFailure (Germ current.old (initial material)) :=
  match initialBirth material with
  | .error failure => .error (.identity failure)
  | .ok birth => admitBirth birth

/-- Renewal preserves retained identity without looking old slots up in a new
body. New keys are generated where actual fresh nodes/primitive directions are born. -/
def renewedGerm {current : Occurrence frame} {prior : Snapshot}
    (germ : Germ current.old prior) (good : prior.Good) (source : Inlet current) :
    Except GermFailure (Germ current.old (renewed prior good source)) :=
  match renewedBirth germ.birth good source with
  | .error failure => .error (.identity failure)
  | .ok birth => admitBirth birth

def Germ.transport {root' : CPS1Deformation.Source.Occurrence frame} {state' : Snapshot}
    (sameRoot : root = root') (sameState : state = state') (germ : Germ root state) : Germ root' state' := by
  cases sameRoot
  cases sameState
  exact germ

def Germ.reprice (germ : Germ root state) (reserve : ℝ) : Germ root (state.reprice reserve) :=
  ⟨germ.birth.reprice reserve,germ.unique,germ.covered,germ.centre,germ.positive,germ.ready⟩

def Germ.withOccupation (germ : Germ root state)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    Germ root (CPS1ReactiveFieldDynamics.withOccupation state coefficients) :=
  ⟨germ.birth.withOccupation coefficients,germ.unique,germ.covered,germ.centre,germ.positive,germ.ready⟩

def Germ.paidResponse (germ : Germ root state) (time : ℝ) :
    Germ root (CPS1ReactiveFieldDynamics.paidResponse state time) :=
  (germ.withOccupation (CPS1ReactiveFieldDynamics.increment state
    (CPS1ReactiveFieldDynamics.responseCoordinates state time))).reprice
      (state.reserve-CPS1ReactiveFieldDynamics.energyDelta state time)

theorem Germ.coefficients_current_square (germ : Germ root state)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    germ.snapshotAt ((germ.positions,germ.momenta),coefficients) =
      CPS1ReactiveFieldDynamics.withOccupation state coefficients := by
  have primitive : germ.primitiveAt germ.positions = state.primitive := funext germ.primitive_current
  have nuclear : List.ofFn (germ.nodeAt germ.positions germ.momenta) = state.nuclei := by
    rw [show germ.nodeAt germ.positions germ.momenta = state.nuclei.get from funext germ.node_current]
    exact List.ofFn_get _
  simp only [Germ.snapshotAt,primitive,nuclear,CPS1ReactiveFieldDynamics.withOccupation]

private def bindActivation (current : Occurrence frame) (active : Active frame)
    (actual : activate current = .ok active) : Except GermFailure (Germ active.source.old active.fields) := do
  let generated := activate_generated current active actual
  let source := generated.choose
  let law := generated.choose_spec
  let material : Material current := ⟨source,incomingReserve source-price source⟩
  let germ ← initialGerm material
  pure (germ.transport (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm)

private def bindRenewal (old : Active frame) (oldGerm : Germ old.source.old old.fields)
    (current : Occurrence frame) (active : Active frame)
    (actual : advance old current = .ok active) : Except GermFailure (Germ active.source.old active.fields) := do
  let generated := advance_generated old current active actual
  let source := generated.choose
  let law := generated.choose_spec
  let currentGerm := oldGerm.transport law.2.2.2.2.2.2.1.symm rfl
  let germ ← renewedGerm currentGerm old.good source
  let priced := germ.reprice (old.fields.reserve+deltaReserve old current-renewalPrice old source)
  pure (priced.transport (congrArg Occurrence.old law.2.1.symm) law.2.2.1.symm)

/-- Missing physical active and a rejected identity germ remain distinct.
The complete original native cursor is retained in every branch. -/
def GermAt (current : Cursor frame) : Type :=
  match current.active with
  | none => PUnit
  | some active => Except GermFailure (Germ active.source.old active.fields)

structure SourceCursor (frame : CPS1Recycling.Frame) where
  native : Cursor frame
  germ : GermAt native

namespace SourceCursor

def start (current : Occurrence frame) : SourceCursor frame := by
  let native := startCursor current
  refine ⟨native,?_⟩
  cases actual : activate current with
  | error failure =>
    simpa only [native,GermAt,startCursor,actual,Except.toOption] using PUnit.unit
  | ok active =>
    simpa only [native,GermAt,startCursor,actual,Except.toOption] using bindActivation current active actual

theorem start_native (current : Occurrence frame) : (start current).native = startCursor current := rfl

/-- The original next is executed once, and the companion is generated over
that exact native result. Retained nuclei never resolve their old numeric slots. -/
def next (current : SourceCursor frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) : SourceCursor frame := by
  let source := CPS1ReactiveField.next current.native.current actions feed raw
  let native := nextCursor current.native actions feed raw
  refine ⟨native,?_⟩
  cases selected : current.native.active with
  | none =>
    cases actual : activate source with
    | error failure =>
      simpa only [native,source,GermAt,nextCursor,selected,actual,Except.toOption,Option.or] using PUnit.unit
    | ok active =>
      simpa only [native,source,GermAt,nextCursor,selected,actual,Except.toOption,Option.or] using
        bindActivation source active actual
  | some old =>
    let oldBinding : Except GermFailure (Germ old.source.old old.fields) := by
      simpa only [GermAt,selected] using current.germ
    cases actual : advance old source with
    | error failure =>
      simpa only [native,source,GermAt,nextCursor,selected,actual,Except.toOption,Option.or] using oldBinding
    | ok active =>
      simpa only [native,source,GermAt,nextCursor,selected,actual,Except.toOption,Option.or] using
        oldBinding.bind (fun oldGerm => bindRenewal old oldGerm source active actual)

theorem next_native (current : SourceCursor frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    (next current actions feed raw).native = nextCursor current.native actions feed raw := rfl

def advanceAll (current : SourceCursor frame) (inputs : List Input) : SourceCursor frame :=
  List.rec (motive := fun _ => SourceCursor frame → SourceCursor frame) (fun current => current)
    (fun input _ recur current => recur (next current input.1.1 input.1.2 input.2)) inputs current

theorem advance_all_native (current : SourceCursor frame) (inputs : List Input) :
    (advanceAll current inputs).native = CPS1ReactiveField.Carried.advanceAll current.native inputs := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    change (advanceAll (next current input.1.1 input.1.2 input.2) rest).native = _
    rw [ih,next_native,CPS1ReactiveField.Carried.advance_all_cons]

theorem actual_atomic_next (current : SourceCursor frame) (inputs : List Input) :
    (advanceAll current inputs).native.current.ingress.atomic =
      CPS1AddressedHydrolysis.Atomic.advanceAll current.native.current.ingress.atomic (inputs.map Prod.fst) := by
  rw [advance_all_native]
  exact CPS1ReactiveField.Carried.advance_all_source _ _

def step (current : SourceCursor frame) :
    Except CPS1ReactiveFieldDynamics.Failure (SourceCursor frame × CPS1ReactiveFieldDynamics.Pulse frame) :=
  match actual : CPS1ReactiveFieldDynamics.step current.native with
  | .error failure => .error failure
  | .ok result => by
    let generated := CPS1ReactiveFieldDynamics.step_generated current.native result.1 result.2 actual
    let valid := generated.2.2.2.2.2.1
    let beforeBinding : Except GermFailure (Germ result.2.before.source.old result.2.before.fields) := by
      simpa only [GermAt,generated.1] using current.germ
    let afterBinding : Except GermFailure (Germ result.2.after.source.old result.2.after.fields) :=
      beforeBinding.map (fun germ => (germ.paidResponse result.2.time).transport
        (congrArg Occurrence.old valid.2.2.1.symm) valid.2.1.symm)
    let binding : GermAt result.1 := by
      simpa only [GermAt,generated.2.2.1] using afterBinding
    exact .ok (⟨result.1,binding⟩,result.2)

theorem step_native (current : SourceCursor frame) :
    (step current).map (fun output => (output.1.native,output.2)) =
      CPS1ReactiveFieldDynamics.step current.native := by
  unfold step
  split <;> rename_i actual <;> simp only [actual,Except.map]

structure Run (frame : CPS1Recycling.Frame) where
  cursor : SourceCursor frame
  pulses : List (CPS1ReactiveFieldDynamics.Pulse frame)
  remaining : Nat
  failure : Option CPS1ReactiveFieldDynamics.Failure

def Run.native (run : Run frame) : CPS1ReactiveFieldDynamics.Run frame :=
  ⟨run.cursor.native,run.pulses,run.remaining,run.failure⟩

def renew (current : SourceCursor frame) (depth : Nat) : Run frame :=
  Nat.rec (motive := fun _ => SourceCursor frame → Run frame)
    (fun current => ⟨current,[],0,none⟩)
    (fun depth recur current => match step current with
      | .error failure => ⟨current,[],depth+1,some failure⟩
      | .ok (next,pulse) => let rest := recur next; {rest with pulses := pulse :: rest.pulses}) depth current

theorem renew_native (current : SourceCursor frame) (depth : Nat) :
    (renew current depth).native = CPS1ReactiveFieldDynamics.renew current.native depth := by
  induction depth generalizing current with
  | zero => rfl
  | succ depth ih =>
    change (match step current with
      | .error failure => (⟨current,[],depth+1,some failure⟩ : Run frame)
      | .ok (next,pulse) => let rest := renew next depth; {rest with pulses := pulse :: rest.pulses}).native = CPS1ReactiveFieldDynamics.renew current.native (depth+1)
    rw [CPS1ReactiveFieldDynamics.renew_succ]
    have projection := step_native current
    cases actual : step current with
    | error failure =>
      simp only [actual,Except.map] at projection
      rw [← projection]
      rfl
    | ok output =>
      rcases output with ⟨next,pulse⟩
      simp only [actual,Except.map] at projection
      rw [← projection]
      change ({(renew next depth).native with pulses := pulse :: (renew next depth).native.pulses} :
          CPS1ReactiveFieldDynamics.Run frame) =
        {CPS1ReactiveFieldDynamics.renew next.native depth with
          pulses := pulse :: (CPS1ReactiveFieldDynamics.renew next.native depth).pulses}
      exact congrArg (fun run : CPS1ReactiveFieldDynamics.Run frame =>
        {run with pulses := pulse :: run.pulses}) (ih next)



end SourceCursor

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
def fromSource (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) :
    Option (Σ frame : CPS1Recycling.Frame, SourceCursor.Run frame) :=
  match CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw with
  | none => none
  | some source => some ⟨source.1,SourceCursor.renew (SourceCursor.start source.2) pulseDepth⟩

def advanceFromSource (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat)
    (inputs : List Input) :
    Option (Σ frame : CPS1Recycling.Frame, SourceCursor.Run frame) :=
  (fromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map (fun current =>
    ⟨current.1,{current.2 with cursor := SourceCursor.advanceAll current.2.cursor inputs}⟩)

theorem admit_birth_generated (birth : Birth root state) (germ : Germ root state)
    (actual : admitBirth birth = .ok germ) : germ.birth = birth := by
  unfold admitBirth at actual
  split at actual
  · split at actual
    · split at actual
      · split at actual
        · split at actual
          · cases Except.ok.inj actual; rfl
          · cases actual
        · cases actual
      · cases actual
    · cases actual
  · cases actual

theorem initial_germ_generated {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) (actual : initialGerm material = .ok germ) :
    (∃ birth, initialBirth material = .ok birth ∧ germ.birth = birth) ∧
    germ.snapshotAt germ.current = initial material ∧
    (∀ slot : OccupiedIndex material.source, ∀ jet, (germ.snapshotAt germ.current).jet slot jet = occupiedJet material.source slot jet) ∧
    germ.energy germ.current = CPS1ReactiveField.energy material.source := by
  unfold initialGerm at actual
  cases born : initialBirth material with
  | error failure => simp only [born] at actual; cases actual
  | ok birth =>
    have paid : admitBirth birth = .ok germ := by simpa only [born] using actual
    refine ⟨⟨birth,rfl,admit_birth_generated birth germ paid⟩,germ.snapshot_current,?_,?_⟩
    · intro slot jet
      exact (germ.jet_current slot jet).trans (initial_jet material slot jet)
    · rw [Germ.energy,germ.snapshot_current]
      exact initial_energy material

theorem renewed_germ_generated {current : Occurrence frame} {prior : Snapshot}
    (old : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (germ : Germ current.old (renewed prior good source))
    (actual : renewedGerm old good source = .ok germ) :
    (∃ birth, renewedBirth old.birth good source = .ok birth ∧ germ.birth = birth) ∧
    germ.snapshotAt germ.current = renewed prior good source ∧
    (∀ slot : prior.ElectronIndex, (germ.snapshotAt germ.current).fields (.inl slot) = prior.fields slot) ∧
    (germ.snapshotAt germ.current).Good ∧
    (germ.snapshotAt germ.current).Ne = prior.Ne+freshCount prior source := by
  unfold renewedGerm at actual
  cases born : renewedBirth old.birth good source with
  | error failure => simp only [born] at actual; cases actual
  | ok birth =>
    have paid : admitBirth birth = .ok germ := by simpa only [born] using actual
    refine ⟨⟨birth,rfl,admit_birth_generated birth germ paid⟩,germ.snapshot_current,?_,?_,?_⟩
    · intro slot
      exact (germ.jet_current (.inl slot) 0).trans (renewed_prefix prior good source slot)
    · exact (congrArg Snapshot.Good germ.snapshot_current).mpr (renewed_good prior good source)
    · exact (congrArg Snapshot.Ne germ.snapshot_current).trans (renewed_Ne prior good source)

theorem actual_renewed_jet_prefix {current : Occurrence frame} (prior : Snapshot)
    (good : prior.Good) (source : Inlet current) (slot : prior.ElectronIndex) (jet : Fin 3 → Nat) :
    (renewed prior good source).jet (.inl slot) jet = prior.jet slot jet := by
  simp only [Snapshot.jet,renewed,renewedCoefficient,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,zero_smul,Finset.sum_const_zero,add_zero]

theorem renewed_germ_complete_prefix {current : Occurrence frame} {prior : Snapshot}
    (old : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (germ : Germ current.old (renewed prior good source))
    (actual : renewedGerm old good source = .ok germ) :
    (∀ slot jet, (germ.snapshotAt germ.current).jet (.inl slot) jet = prior.jet slot jet) ∧
    (∃ fresh, germ.birth.nuclearKeys = old.birth.nuclearKeys ++ fresh) ∧
    (∀ primitive, germ.birth.primitiveKey (.inl primitive) = old.birth.primitiveKey primitive) ∧
    germ.energy germ.current = (renewed prior good source).energy := by
  have generated := renewed_germ_generated old good source germ actual
  obtain ⟨birth,born,same⟩ := generated.1
  have keys := renewed_birth_generated old.birth good source birth born
  refine ⟨?_,?_,?_,?_⟩
  · intro slot jet
    exact (germ.jet_current (.inl slot) jet).trans (actual_renewed_jet_prefix prior good source slot jet)
  · obtain ⟨fresh,_,identity⟩ := keys.2.2.1
    exact ⟨fresh,(congrArg Birth.nuclearKeys same).trans identity⟩
  · intro primitive
    rw [same]
    exact keys.2.2.2.1 primitive
  · rw [Germ.energy,germ.snapshot_current]

end
end CPS1ReactiveNuclear
