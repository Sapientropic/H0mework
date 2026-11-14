import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ReachableWords
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3CompleteInventory

set_option autoImplicit false
namespace FlyCNS.C3FiniteOccurrence
open C3Reachable

abbrev RootSource := SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.ContentReentryIO.Source
abbrev Inventory := SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3CompleteInventory.Image
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS

structure Boundary where
  private mk ::
  source : RootSource
  seed : Seed
  decoded : C3Reachable.fromRoot source=.ok seed
  latestTraces : Vector ByteArray 3

structure Installed (boundary : Boundary) where
  private mk ::
  material : C3BoundKernel.Installation
  instanceId : material.identity.instanceId=boundary.source.material.instanceId
  occurrenceId : material.identity.occurrenceId=boundary.source.material.occurrenceId
  installationId : material.identity.installationId=boundary.source.material.installationId

def bindInstallation (boundary : Boundary) (material : C3BoundKernel.Installation) : Except String (Installed boundary) :=
  if instanceId:material.identity.instanceId=boundary.source.material.instanceId then
    if occurrenceId:material.identity.occurrenceId=boundary.source.material.occurrenceId then
      if installationId:material.identity.installationId=boundary.source.material.installationId then
        .ok ⟨material,instanceId,occurrenceId,installationId⟩
      else .error "finite carrier changed the original installation"
    else .error "finite carrier changed the original birth occurrence"
  else .error "finite carrier changed the original actor"

def install (boundary : Boundary) : IO (Installed boundary) := do
  let material ← ContentReentryIO.installPure boundary.source
  BodyIO.checkedResult (bindInstallation boundary material)

/-- The existing opaque Source selects its original complete current2 and
its three recorded traces. No directory, state or future output is selected. -/
def readBoundary (source : RootSource) : IO Boundary := do
  match decoded:C3Reachable.fromRoot source with
  | .error why => throw (IO.userError why)
  | .ok admitted =>
    let directory:=source.material.physicalDirectory/"observed-2"
    let original ← ContentReentryIO.readCurrent source.material directory
    if ContentReentryIO.capture original != ContentReentryIO.capture source.initial then
      throw (IO.userError "finite carrier traces belong to another complete boundary")
    let events ← IO.FS.readBinFile (directory/"generated-events.npz")
    let learning ← IO.FS.readBinFile (directory/"learning-trace.npz")
    let physics ← IO.FS.readBinFile (directory/"physics-trace.npz")
    return ⟨source,admitted,decoded,⟨#[events,learning,physics],rfl⟩⟩

def initialImage (boundary : Boundary) : Inventory :=
  ⟨ContentReentryIO.capture boundary.source.initial,boundary.latestTraces,C3CompleteInventory.sourceMetadata boundary.source⟩

/-- The original typed Current parser interprets only source-written output.
All three literal traces and every original material are kept in the image. -/
def producedImage (boundary : Boundary) (generated : C3Published.Result) : Except String Inventory := do
  let current ← C3RootSplice.current boundary.source generated.numerical
  return ⟨ContentReentryIO.capture current,
    ⟨#[generated.numerical.events,generated.learning,generated.numerical.physics.getD ByteArray.empty],rfl⟩,
    C3CompleteInventory.sourceMetadata boundary.source⟩

def image (boundary : Boundary) : Except String (Option C3Published.Result) → Except String Inventory
  | .error why => .error why
  | .ok none => .ok (initialImage boundary)
  | .ok (some generated) => producedImage boundary generated

def occurrenceCurrent (seed : Seed) : Option C3Published.Result → C3Successful.Current
  | none => seed.initial
  | some generated => generated.numerical.current

def occurrenceAction (material : C3Macro.Material) (seed : Seed)
    (operation : C3Native.Operation) (current : Except String (Option C3Published.Result)) :
    Except String (Option C3Published.Result) := do
  let before ← current
  let generated ← C3Published.action material operation (occurrenceCurrent seed before)
  return some generated

def generate (material : C3Macro.Material) (seed : Seed) : Nat → Except String (Option C3Published.Result)
  | 0 => .ok none
  | n+1 => do
    let before ← generate material seed n
    let generated ← C3Published.successor material (occurrenceCurrent seed before)
    return some generated

theorem published_numerical {generated : C3Successful.Result} {published : C3Published.Result}
    (paid : C3Published.publish generated=.ok published) : published.numerical=generated := by
  unfold C3Published.publish at paid
  simp only [bind,pure,Except.bind,Except.pure] at paid
  cases h:generated.learning with
  | none => simp only [h] at paid;cases paid;rfl
  | some members =>
    simp only [h] at paid
    cases hc:C3CompressedTrace.generate members with
    | error why => simp only [hc] at paid;contradiction
    | ok bytes => simp only [hc] at paid;cases paid;rfl

theorem published_original {material : C3Macro.Material} {operation : C3Native.Operation}
    {before : C3Successful.Current} {published : C3Published.Result}
    (paid : C3Published.action material operation before=.ok published) :
    C3Successful.action material operation before=.ok published.numerical := by
  unfold C3Published.action at paid
  simp only [bind,Except.bind] at paid
  cases h:C3Successful.action material operation before with
  | error why => simp only [h] at paid;contradiction
  | ok generated =>
    simp only [h] at paid
    rw [published_numerical paid]

theorem generated_reachable {material : C3Macro.Material} {seed : Seed}
    {n : Nat} {current : Option C3Published.Result}
    (paid : generate material seed n=.ok current) :
    C3Reachable.Reachable material seed.initial n (occurrenceCurrent seed current) := by
  induction n generalizing current with
  | zero => cases paid;exact .initial
  | succ n previous =>
    simp only [generate,bind,pure,Except.bind,Except.pure] at paid
    cases hb:generate material seed n with
    | error why => simp only [hb] at paid;contradiction
    | ok before =>
      simp only [hb] at paid
      cases hg:C3Published.successor material (occurrenceCurrent seed before) with
      | error why => simp only [hg] at paid;contradiction
      | ok generated =>
        simp only [hg] at paid
        cases paid
        exact .next (previous hb) (published_original hg)

theorem generated_bound {material : C3Macro.Material} {seed : Seed}
    {n : Nat} {current : Option C3Published.Result}
    (paid : generate material seed n=.ok current) : n+2<stateBound := by
  have reachable:=generated_reachable paid
  have bound:=reachable_visit_bound seed.clock seed.signed_bound reachable
  have visit:=reachable_visit reachable
  rw [seed.visit] at visit
  unfold stateBound
  omega

theorem generated_visit {material : C3Macro.Material} {seed : Seed}
    {n : Nat} {current : Option C3Published.Result}
    (paid : generate material seed n=.ok current) :
    (occurrenceCurrent seed current).original.visit=2+n := by
  simpa only [seed.visit] using reachable_visit (generated_reachable paid)

theorem terminal (material : C3Macro.Material) (seed : Seed) :
    ∃ why,generate material seed stateBound=.error why := by
  cases h:generate material seed stateBound with
  | error why => exact ⟨why,rfl⟩
  | ok current => have bad:=generated_bound h;omega

def indexed (material : C3Macro.Material) (seed : Seed) (index : Fin (stateBound+2)) :
    Except String (Option C3Published.Result) :=
  if index.val<stateBound then generate material seed index.val
  else if index.val=stateBound then generate material seed stateBound
  else .error "operation not admitted at this source incidence"

theorem indexed_ok_below {material : C3Macro.Material} {seed : Seed}
    {index : Fin (stateBound+2)} {current : Option C3Published.Result}
    (paid : indexed material seed index=.ok current) : index.val<stateBound := by
  unfold indexed at paid
  split at paid
  · assumption
  · split at paid
    · rcases terminal material seed with ⟨why,failed⟩
      rw [failed] at paid;contradiction
    · contradiction

def action (material : C3Macro.Material) (seed : Seed) (operation : C3Native.Operation)
    (index : Fin (stateBound+2)) : Fin (stateBound+2) :=
  match paid:indexed material seed index with
  | .error _ => index
  | .ok current =>
    if C3Native.operationAt (occurrenceCurrent seed current).original.visit=operation then
      ⟨index.val+1,by have below:=indexed_ok_below paid;omega⟩
    else ⟨stateBound+1,by omega⟩

theorem published_wrong (material : C3Macro.Material) (before : C3Successful.Current)
    (operation : C3Native.Operation) (wrong : C3Native.operationAt before.original.visit≠operation) :
    C3Published.action material operation before=.error "operation not admitted at this source incidence" := by
  simp only [C3Published.action,C3Reachable.wrong_letter material before operation wrong,bind,Except.bind]

theorem action_commutes (material : C3Macro.Material) (seed : Seed)
    (operation : C3Native.Operation) (index : Fin (stateBound+2)) :
    indexed material seed (action material seed operation index)=occurrenceAction material seed operation (indexed material seed index) := by
  unfold action
  split
  next why failed => simp_all only [occurrenceAction,bind,Except.bind]
  next before accepted =>
    have below:=indexed_ok_below accepted
    have original:generate material seed index.val=.ok before := by
      simpa only [indexed,if_pos below] using accepted
    split
    next legal =>
      have bound:=generated_bound original
      have last:index.val+1<stateBound := by omega
      simp only [indexed,if_pos last,if_pos below]
      change (do
        let previous ← generate material seed index.val
        let produced ← C3Published.successor material (occurrenceCurrent seed previous)
        pure (some produced))=_
      rw [original]
      simp only [occurrenceAction,bind,Except.bind]
      rw [← legal]
      rfl
    next wrong =>
      have failed:=published_wrong material (occurrenceCurrent seed before) operation wrong
      simp only [indexed,show ¬stateBound+1<stateBound by omega,
        show stateBound+1≠stateBound by omega,if_false,if_pos below,original,occurrenceAction,bind,Except.bind,failed]

def execute (material : C3Macro.Material) (seed : Seed) : List C3Native.Operation →
    Except String (Option C3Published.Result) → Except String (Option C3Published.Result)
  | [],current => current
  | operation::rest,current => execute material seed rest (occurrenceAction material seed operation current)

theorem all_words (material : C3Macro.Material) (seed : Seed) (word : List C3Native.Operation)
    (index : Fin (stateBound+2)) :
    indexed material seed (WholeRepresentation.runMap (action material seed) word index)=
      execute material seed word (indexed material seed index) := by
  induction word generalizing index with
  | nil => rfl
  | cons operation rest previous =>
    simp only [WholeRepresentation.runMap,execute]
    rw [previous,action_commutes]

theorem execute_error (material : C3Macro.Material) (seed : Seed) (word : List C3Native.Operation) (why : String) :
    execute material seed word (.error why)=.error why := by
  induction word with
  | nil => rfl
  | cons _ _ previous => simpa only [execute,occurrenceAction,bind,Except.bind] using previous

theorem execute_original (material : C3Macro.Material) (seed : Seed) (word : List C3Native.Operation)
    (current : Option C3Published.Result) :
    (execute material seed word (.ok current)).map (occurrenceCurrent seed)=
      C3Published.word material word (occurrenceCurrent seed current) := by
  induction word generalizing current with
  | nil => rfl
  | cons operation rest previous =>
    simp only [execute,occurrenceAction,C3Published.word,bind,pure,Except.bind,Except.pure]
    cases h:C3Published.action material operation (occurrenceCurrent seed current) with
    | error why => rw [execute_error];rfl
    | ok generated => exact previous (some generated)

theorem complete_generated_coverage (material : C3Macro.Material) (seed : Seed)
    {n : Nat} {current : Option C3Published.Result}
    (paid : generate material seed n=.ok current) :
    ∃ index : Fin (stateBound+2),indexed material seed index=.ok current := by
  have bound:=generated_bound paid
  refine ⟨⟨n,by omega⟩,?_⟩
  have below:n<stateBound := by omega
  simp only [indexed,if_pos below]
  exact paid

theorem index_restores_complete (material : C3Macro.Material) (seed : Seed)
    {left right : Fin (stateBound+2)} {a b : Option C3Published.Result}
    (first:indexed material seed left=.ok a) (second:indexed material seed right=.ok b)
    (visit:(occurrenceCurrent seed a).original.visit=(occurrenceCurrent seed b).original.visit) : a=b := by
  have leftBelow:=indexed_ok_below first
  have rightBelow:=indexed_ok_below second
  have ha:generate material seed left.val=.ok a := by simpa only [indexed,if_pos leftBelow] using first
  have hb:generate material seed right.val=.ok b := by simpa only [indexed,if_pos rightBelow] using second
  have va:=generated_visit ha
  have vb:=generated_visit hb
  have address:left.val=right.val := by omega
  rw [address] at ha
  exact Except.ok.inj (ha.symm.trans hb)

end FlyCNS.C3FiniteOccurrence
