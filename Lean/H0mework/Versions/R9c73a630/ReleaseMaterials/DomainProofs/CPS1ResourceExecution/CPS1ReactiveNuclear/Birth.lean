import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Renewal
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Basis
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveNuclear
noncomputable section
open CPS1ElectronicSource
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

/-- Physical identities are indexed by the same original source occurrence. -/
inductive Key (root : CPS1Deformation.Source.Occurrence frame)
  | enzyme (source : CPS1AtomicSource.Graph.Atom)
  | bath (component : CPS1EnzymeBath.Joint.Component) (source : CPS1EnzymeBath.Primary.Atom)
  | water (source : CPS1AddressedHydrolysis.Water) (atom : CPS1AddressedHydrolysis.WaterAtom)
  deriving DecidableEq

inductive IdentityFailure
  | unknownLegacy (address : CPS1AtomicDynamics.Charged.Address)
  | legacyDescriptor (address : CPS1AtomicDynamics.Charged.Address)
  | unknownSeededOld (slot : Nat)
  | unknownReactiveNucleus (address : CPS1AtomicDynamics.Charged.Address)
  | reactiveDescriptor (address : CPS1AtomicDynamics.Charged.Address)
  | expectedWater (origin : CPS1AddressedHydrolysis.Origin)
  | incompletePrimitiveOrigins
  | differentOldCarrier
  deriving DecidableEq

private def jointKey (root : CPS1Deformation.Source.Occurrence frame)
    (origin : CPS1EnzymeBath.Joint.AtomOrigin) : Key root :=
  match origin with
  | .enzyme source => .enzyme source
  | .bath component source => .bath component source

private def legacyKey? (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame) (address : CPS1AtomicDynamics.Charged.Address) :
    Except IdentityFailure (Key root) :=
  match address with
  | .electron .. => .error (.unknownLegacy address)
  | .nucleus slot =>
    match (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot]? with
    | none => .error (.unknownLegacy address)
    | some atom => .ok (jointKey root atom.origin)

private def legacyNodeKey? (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame) (node : CPS1AtomicDynamics.Body.Node) :
    Except IdentityFailure (Key root) :=
  match node.particle.address with
  | .electron .. => .error (.unknownLegacy node.particle.address)
  | .nucleus slot =>
    match (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot]? with
    | none => .error (.unknownLegacy node.particle.address)
    | some atom =>
      if node.particle.source = atom.descriptor then .ok (jointKey root atom.origin)
      else .error (.legacyDescriptor node.particle.address)

/-- Only the initial seeded graph interprets `.old`. Current Graph slots do not. -/
private def reactiveKey? (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame) (origin : CPS1AddressedHydrolysis.Origin) :
    Except IdentityFailure (Key root) :=
  match origin with
  | .old slot =>
    match (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms[slot]? with
    | none => .error (.unknownSeededOld slot)
    | some source => .ok (.enzyme source)
  | .water source atom => .ok (.water source atom)

private def primitiveKey? (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame) (origin : PrimitiveOrigin) :
    Except IdentityFailure (Key root) :=
  match origin with
  | .legacy address => legacyKey? root owner address
  | .reactive origin => reactiveKey? root owner origin

private def waterNodeKey? {current : Occurrence frame} (source : Inlet current)
    (node : CPS1AtomicDynamics.Body.Node) : Except IdentityFailure (Key current.old) :=
  match node.particle.address with
  | .electron .. => .error (.unknownReactiveNucleus node.particle.address)
  | .nucleus slot =>
    match source.body.atoms[slot]? with
    | none => .error (.unknownReactiveNucleus node.particle.address)
    | some atom =>
      if node.particle.source ≠ atom.descriptor then .error (.reactiveDescriptor node.particle.address)
      else match atom.origin with
      | .old _ => .error (.expectedWater atom.origin)
      | .water water atom => .ok (.water water atom)

private structure BoundList {α : Type} (root : CPS1Deformation.Source.Occurrence frame)
    (nodes : List α) where
  keys : List (Key root)
  length_eq : keys.length = nodes.length

private def bindList {α : Type} {root : CPS1Deformation.Source.Occurrence frame}
    (resolve : α → Except IdentityFailure (Key root)) :
    (nodes : List α) → Except IdentityFailure (BoundList root nodes)
  | [] => .ok ⟨[],rfl⟩
  | node :: rest => do
    let key ← resolve node
    let tail ← bindList resolve rest
    pure ⟨key :: tail.keys,by simpa only [List.length_cons] using congrArg Nat.succ tail.length_eq⟩

private def bindPrimitives {ι : Type} [Fintype ι]
    {root : CPS1Deformation.Source.Occurrence frame}
    (resolve : ι → Except IdentityFailure (Key root)) : Except IdentityFailure (ι → Key root) := by
  classical
  exact if complete : ∀ index, (resolve index).toOption.isSome = true then
    .ok (fun index => (resolve index).toOption.get (complete index))
  else .error .incompletePrimitiveOrigins

/-- This companion is allocated at initial/renewal birth. Retained numeric
readouts are never resolved against a later body's current slot ordering. -/
structure Birth (root : CPS1Deformation.Source.Occurrence frame) (state : Snapshot) where
  owner : CPS1Deformation.Material frame
  ownerHeld : CPS1Deformation.Species.deformed owner ∈ root.current.stock
  nuclearKeys : List (Key root)
  nuclearLength : nuclearKeys.length = state.nuclei.length
  primitiveKey : state.PrimitiveIndex → Key root

def initialBirth {current : Occurrence frame} (material : Material current) :
    Except IdentityFailure (Birth current.old (initial material)) := do
  let old ← bindList (legacyNodeKey? current.old material.source.old)
    (List.ofFn (oldNuclearNode material.source))
  let water ← bindList (waterNodeKey? material.source) ((waterNodes material.source).filter isNucleus)
  let primitive ← bindPrimitives (fun index : CommonPrimitive material.source =>
    primitiveKey? current.old material.source.old (initialPrimitive material.source index).origin)
  pure ⟨material.source.old,material.source.held,old.keys ++ water.keys,
    by simpa only [initial,commonNuclei,List.length_append] using
      congrArg₂ (fun a b : Nat => a+b) old.length_eq water.length_eq,primitive⟩

def renewedBirth {current : Occurrence frame} {state : Snapshot}
    (old : Birth current.old state) (good : state.Good) (source : Inlet current) :
    Except IdentityFailure (Birth current.old (renewed state good source)) := by
  classical
  exact if source.old ≠ old.owner then .error .differentOldCarrier else do
    let water ← bindList (waterNodeKey? source) ((freshNodes state source).filter isNucleus)
    let primitive ← bindPrimitives (fun index : RenewalPrimitive state source =>
      primitiveKey? current.old old.owner (renewalPrimitive state source index).origin)
    pure ⟨old.owner,old.ownerHeld,old.nuclearKeys ++ water.keys,
      by simpa only [renewed,List.length_append,old.nuclearLength] using
        congrArg (fun count => state.nuclei.length+count) water.length_eq,
      Sum.elim old.primitiveKey primitive⟩

def Birth.reprice {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (birth : Birth root state) (reserve : ℝ) : Birth root (state.reprice reserve) :=
  ⟨birth.owner,birth.ownerHeld,birth.nuclearKeys,birth.nuclearLength,birth.primitiveKey⟩

def Birth.withOccupation {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (birth : Birth root state) (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    Birth root (CPS1ReactiveFieldDynamics.withOccupation state coefficients) :=
  ⟨birth.owner,birth.ownerHeld,birth.nuclearKeys,birth.nuclearLength,birth.primitiveKey⟩

private theorem bind_list_generated {α : Type} {root : CPS1Deformation.Source.Occurrence frame}
    (resolve : α → Except IdentityFailure (Key root)) (nodes : List α) (bound : BoundList root nodes)
    (actual : bindList resolve nodes = .ok bound) :
    List.Forall₂ (fun node key => resolve node = .ok key) nodes bound.keys := by
  induction nodes with
  | nil =>
    simp only [bindList] at actual
    cases Except.ok.inj actual
    exact .nil
  | cons node rest ih =>
    cases head : resolve node with
    | error failure => simp only [bindList,head] at actual; cases actual
    | ok key =>
      cases tail : bindList resolve rest with
      | error failure => simp only [bindList,head,tail] at actual; cases actual
      | ok generated =>
        simp only [bindList,head,tail] at actual
        cases Except.ok.inj actual
        exact .cons head (ih generated tail)

private theorem bind_primitives_generated {ι : Type} [Fintype ι]
    {root : CPS1Deformation.Source.Occurrence frame}
    (resolve : ι → Except IdentityFailure (Key root)) (bound : ι → Key root)
    (actual : bindPrimitives resolve = .ok bound) : ∀ index, resolve index = .ok (bound index) := by
  unfold bindPrimitives at actual
  split at actual
  · rename_i complete
    cases Except.ok.inj actual
    intro index
    cases generated : resolve index with
    | error failure => have paid := complete index; simp [generated,Except.toOption] at paid
    | ok key => simp [generated,Except.toOption]
  · cases actual

theorem initial_birth_generated {current : Occurrence frame} (material : Material current)
    (birth : Birth current.old (initial material)) (actual : initialBirth material = .ok birth) :
    birth.owner = material.source.old ∧
    (∃ old water,
      List.Forall₂ (fun node key => legacyNodeKey? current.old material.source.old node = .ok key)
        (List.ofFn (oldNuclearNode material.source)) old ∧
      List.Forall₂ (fun node key => waterNodeKey? material.source node = .ok key)
        ((waterNodes material.source).filter isNucleus) water ∧
      birth.nuclearKeys = old ++ water) ∧
    (∀ primitive, primitiveKey? current.old material.source.old
      (initialPrimitive material.source primitive).origin = .ok (birth.primitiveKey primitive)) := by
  unfold initialBirth at actual
  cases oldResult : bindList (legacyNodeKey? current.old material.source.old)
      (List.ofFn (oldNuclearNode material.source)) with
  | error failure => simp only [oldResult] at actual; cases actual
  | ok old =>
    cases waterResult : bindList (waterNodeKey? material.source) ((waterNodes material.source).filter isNucleus) with
    | error failure => simp only [oldResult,waterResult] at actual; cases actual
    | ok water =>
      cases primitiveResult : bindPrimitives (fun index : CommonPrimitive material.source =>
          primitiveKey? current.old material.source.old (initialPrimitive material.source index).origin) with
      | error failure => simp only [oldResult,waterResult,primitiveResult] at actual; cases actual
      | ok primitive =>
        simp only [oldResult,waterResult,primitiveResult] at actual
        cases Except.ok.inj actual
        exact ⟨rfl,⟨old.keys,water.keys,bind_list_generated _ _ old oldResult,
          bind_list_generated _ _ water waterResult,rfl⟩,
          bind_primitives_generated _ primitive primitiveResult⟩

theorem renewed_birth_generated {current : Occurrence frame} {state : Snapshot}
    (old : Birth current.old state) (good : state.Good) (source : Inlet current)
    (birth : Birth current.old (renewed state good source))
    (actual : renewedBirth old good source = .ok birth) :
    source.old = old.owner ∧ birth.owner = old.owner ∧
    (∃ water,
      List.Forall₂ (fun node key => waterNodeKey? source node = .ok key)
        ((freshNodes state source).filter isNucleus) water ∧
      birth.nuclearKeys = old.nuclearKeys ++ water) ∧
    (∀ primitive, birth.primitiveKey (.inl primitive) = old.primitiveKey primitive) ∧
    (∀ primitive, primitiveKey? current.old old.owner (renewalPrimitive state source primitive).origin =
      .ok (birth.primitiveKey (.inr primitive))) := by
  unfold renewedBirth at actual
  split at actual
  · cases actual
  · rename_i same
    cases waterResult : bindList (waterNodeKey? source) ((freshNodes state source).filter isNucleus) with
    | error failure => simp only [waterResult] at actual; cases actual
    | ok water =>
      cases primitiveResult : bindPrimitives (fun index : RenewalPrimitive state source =>
          primitiveKey? current.old old.owner (renewalPrimitive state source index).origin) with
      | error failure => simp only [waterResult,primitiveResult] at actual; cases actual
      | ok primitive =>
        simp only [waterResult,primitiveResult] at actual
        cases Except.ok.inj actual
        exact ⟨not_not.mp same,rfl,⟨water.keys,bind_list_generated _ _ water waterResult,rfl⟩,
          fun _ => rfl,bind_primitives_generated _ primitive primitiveResult⟩

theorem occupation_birth_retained {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (birth : Birth root state) (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) (reserve : ℝ) :
    ((birth.withOccupation coefficients).reprice reserve).owner = birth.owner ∧
    ((birth.withOccupation coefficients).reprice reserve).nuclearKeys = birth.nuclearKeys ∧
    ((birth.withOccupation coefficients).reprice reserve).primitiveKey = birth.primitiveKey := ⟨rfl,rfl,rfl⟩

/-- The enzyme prefix and the initial seeded old-origin slot name the same
actual source atom. Bath is retained by the other `jointKey` constructor. -/
theorem enzyme_seeded_key (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame)
    (slot : Fin (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms.length) :
    let source := (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms.get slot
    legacyKey? root owner (.nucleus slot.val) = .ok (.enzyme source) ∧
    reactiveKey? root owner (.old slot.val) = .ok (.enzyme source) := by
  have selected : (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot.val]? =
      some ⟨.enzyme ((CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms.get slot),
        (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms.get slot⟩ := by
    simp only [CPS1EnzymeBath.Joint.atoms,CPS1AtomicDynamics.Body.graph,CPS1AtomicSource.Current.graph]
    rw [List.getElem?_append_left (by simpa only [List.length_map] using slot.isLt),List.getElem?_map]
    simp only [List.getElem?_eq_getElem slot.isLt,List.get_eq_getElem,Option.map_some]
  simp only [legacyKey?,selected,jointKey,reactiveKey?,List.getElem?_eq_getElem slot.isLt,List.get_eq_getElem]
  exact ⟨True.intro,True.intro⟩

theorem actual_water_key (root : CPS1Deformation.Source.Occurrence frame)
    (owner : CPS1Deformation.Material frame) (water : CPS1AddressedHydrolysis.Water)
    (atom : CPS1AddressedHydrolysis.WaterAtom) :
    reactiveKey? root owner (.water water atom) = .ok (.water water atom) := rfl

/-- This exact raw-source seam preserves the initially copied actual old rows.
Identity equality does not appear as a premise or imply coordinate equality. -/
theorem actual_legacy_rows_preserved (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    ∀ address row, CPS1AddressedReactiveJoint.Rows.row? (legacyRows old) address = some row →
      CPS1AddressedReactiveJoint.Rows.row?
        (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw).ingress.measurements.rows
        address = some row := by
  exact CPS1AddressedReactiveJoint.Rows.run_rows_preserved _ ⟨legacyRows old,0⟩ _

theorem legacy_primitive_current_position {current : Occurrence frame} (source : Inlet current)
    (nuclear : CPS1MolecularFrame.NuclearIndex source.old.reference)
    (mode : CPS1MolecularFrame.ModeIndex source.old.reference) (spin : Bool) :
    (initialPrimitive source (.inl ((nuclear,mode),spin))).centre =
      Geometry.nucleusPosition (oldNuclearNode source nuclear) := rfl

end
end CPS1ReactiveNuclear
