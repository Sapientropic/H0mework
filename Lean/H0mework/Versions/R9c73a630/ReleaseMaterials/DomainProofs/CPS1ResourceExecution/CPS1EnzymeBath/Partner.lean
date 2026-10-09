import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.BathAccounting

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1EnzymeBath.Partner
noncomputable section

theorem capture_cp_present (frame : CPS1Recycling.Frame)
    (previous : CPS1AtomicDynamics.Source.Occurrence frame)
    (body : CPS1AtomicDynamics.Body.State frame)
    (held : CPS1AtomicDynamics.Source.heldBody frame previous.current.stock = some body)
    (cp : BathAccounting.currentCp frame ∈ previous.current.stock) :
    componentSpecies frame .carbamoylPhosphate ∈ (Source.start frame previous).stock := by
  have distinct : BathAccounting.currentCp frame ≠ CPS1AtomicDynamics.Species.body body := by
    simp [BathAccounting.currentCp]
  have kept : BathAccounting.currentCp frame ∈ previous.current.stock.erase (.body body) :=
    (List.mem_erase_of_ne distinct).mpr cp
  have mapped : componentSpecies frame .carbamoylPhosphate ∈
      (previous.current.stock.erase (.body body)).map (Source.liftMaterial frame) := by
    exact List.mem_map.mpr ⟨_,kept,rfl⟩
  exact (Actual.capture_live_body frame previous body held).1.mem_iff.mpr
    (List.mem_cons_of_mem _ mapped)

theorem capture_head (frame : CPS1Recycling.Frame)
    (previous : CPS1AtomicDynamics.Source.Occurrence frame)
    (body : CPS1AtomicDynamics.Body.State frame)
    (held : CPS1AtomicDynamics.Source.heldBody frame previous.current.stock = some body) :
    ∃ surplus, (Source.start frame previous).stock = .joint (Joint.fromBody frame body) :: surplus ∧
      surplus.Perm ((previous.current.stock.erase (.body body)).map (Source.liftMaterial frame)) := by
  let lifted := previous.current.stock.map (Source.liftMaterial frame)
  have present : Species.retained (.body body) ∈ lifted :=
    List.mem_map.mpr ⟨_,Actual.body_member frame _ body held,rfl⟩
  have paid : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      (.capture body) lifted = .ok (.joint (Joint.fromBody frame body) :: lifted.erase (.retained (.body body))) := by
    simp [CPS1ResourceExecution.Inventory.fire,Reaction.reactants,Reaction.products,
      CPS1ResourceExecution.Inventory.consume,present]
  have head : (Source.start frame previous).stock =
      .joint (Joint.fromBody frame body) :: lifted.erase (.retained (.body body)) := by
    simp only [Source.start,held,execute,CPS1ResourceExecution.Inventory.execute]
    dsimp only [lifted] at paid
    rw [paid]
  have aligned := (Actual.capture_live_body frame previous body held).1
  rw [head] at aligned
  exact ⟨_,head,List.Perm.cons_inv aligned⟩

theorem program_cons (frame : CPS1Recycling.Frame) (state : Joint.State frame)
    (action : Source.RawAction) (actions : List Source.RawAction) :
    Source.program frame state (action :: actions) =
      action.reaction frame state :: Source.program frame (action.next frame state) actions := rfl

theorem advance_partner (frame : CPS1Recycling.Frame) (cursor : Source.Cursor frame)
    (state : Joint.State frame) (initialSurplus : Stock frame)
    (head : cursor.stock = .joint state :: initialSurplus)
    (captured : cursor.captureRemaining = [])
    (cp : componentSpecies frame .carbamoylPhosphate ∈ cursor.stock)
    (actions : List Source.RawAction) (feed : List Primary.TemplateKind) :
    let available := cursor.stock ++ feed.map (Source.rawComponent frame) ++
      actions.flatMap (Source.RawAction.material frame)
    let next := Source.advance frame cursor (Source.generatedPartnerProgram ++ actions) feed
    ∃ surplus,
      available.Perm ([.joint state,componentSpecies frame .carbamoylPhosphate] ++ surplus) ∧
      let after := execute frame
        (Source.program frame (Joint.attach frame state .carbamoylPhosphate) (actions ++ cursor.pending))
        (.joint (Joint.attach frame state .carbamoylPhosphate) :: surplus)
      next.stock = after.stock ∧
      next.stages = cursor.stages ++ [{after with fired := .attach state .carbamoylPhosphate :: after.fired}] ∧
      next.captureRemaining = [] ∧ next.cut = after.missing := by
  dsimp only
  let available := cursor.stock ++ feed.map (Source.rawComponent frame) ++
    actions.flatMap (Source.RawAction.material frame)
  have jointPresent : Species.joint state ∈ available := by
    apply List.mem_append_left
    apply List.mem_append_left
    rw [head]
    exact List.mem_cons_self
  have cpPresent : componentSpecies frame .carbamoylPhosphate ∈ available :=
    List.mem_append_left _ (List.mem_append_left _ cp)
  have cpRemaining : componentSpecies frame .carbamoylPhosphate ∈ available.erase (.joint state) :=
    (List.mem_erase_of_ne (by simp [componentSpecies])).mpr cpPresent
  let surplus := (available.erase (.joint state)).erase (componentSpecies frame .carbamoylPhosphate)
  have reserved : CPS1ResourceExecution.Inventory.consume
      [.joint state,componentSpecies frame .carbamoylPhosphate] available = .ok surplus := by
    simp [CPS1ResourceExecution.Inventory.consume,jointPresent,cpRemaining,surplus]
  have inventory := CPS1ResourceExecution.Inventory.consume_perm _ _ _ reserved
  have paid : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      (.attach state .carbamoylPhosphate) available =
      .ok (.joint (Joint.attach frame state .carbamoylPhosphate) :: surplus) := by
    simp only [CPS1ResourceExecution.Inventory.fire,Reaction.reactants,reserved,Reaction.products,List.singleton_append]
  have held : Source.heldJoint frame available = some state := by
    simp only [available,head,List.cons_append,Source.heldJoint]
  let after := execute frame
    (Source.program frame (Joint.attach frame state .carbamoylPhosphate) (actions ++ cursor.pending))
    (.joint (Joint.attach frame state .carbamoylPhosphate) :: surplus)
  have actual : execute frame
      (Source.program frame state ((Source.generatedPartnerProgram ++ actions) ++ cursor.pending)) available =
      {after with fired := .attach state .carbamoylPhosphate :: after.fired} := by
    change execute frame (.attach state .carbamoylPhosphate ::
      Source.program frame (Joint.attach frame state .carbamoylPhosphate) (actions ++ cursor.pending)) available = _
    rw [execute,CPS1ResourceExecution.Inventory.execute_cons,paid]
    rfl
  simp only [Source.generatedPartnerProgram,List.singleton_append] at actual
  dsimp only [available] at held actual
  refine ⟨surplus,inventory,?_,?_,?_,?_⟩
  · simp only [Source.advance,Source.generatedPartnerProgram,List.singleton_append,List.flatMap_cons,
      Source.RawAction.material,List.nil_append,captured]
    rw [held]
    dsimp only
    have projected := congrArg (fun result : Execution frame => result.stock) actual
    exact projected
  · simp only [Source.advance,Source.generatedPartnerProgram,List.singleton_append,List.flatMap_cons,
      Source.RawAction.material,List.nil_append,captured]
    rw [held]
    dsimp only
    exact congrArg (fun result : Execution frame => cursor.stages ++ [result]) actual
  · simp only [Source.advance,captured,List.drop_nil]
  ·
    simp only [Source.advance,Source.generatedPartnerProgram,List.singleton_append,List.flatMap_cons,
      Source.RawAction.material,List.nil_append,captured]
    rw [held]
    dsimp only
    have projected := congrArg (fun result : Execution frame => result.missing) actual
    exact projected

theorem actual_generated_partner
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm
      (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (actions : List Source.RawAction) (feed : List Primary.TemplateKind) :
    ∃ (frame : CPS1Recycling.Frame) (next : Source.Occurrence frame)
      (body : CPS1AtomicDynamics.Body.State frame) (surplus : Stock frame),
      Source.generatedExecution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions actions feed = some ⟨frame,next⟩ ∧
      CPS1AtomicDynamics.Source.heldBody frame next.previous.current.stock = some body ∧
      (Source.start frame next.previous).pending = next.previous.current.pending.map Source.liftBodyAction ∧
      let initial := Joint.fromBody frame body
      let available := (Source.start frame next.previous).stock ++ feed.map (Source.rawComponent frame) ++
        actions.flatMap (Source.RawAction.material frame)
      available.Perm ([.joint initial,componentSpecies frame .carbamoylPhosphate] ++ surplus) ∧
      let partnered := Joint.attach frame initial .carbamoylPhosphate
      partnered.originBody = body ∧ partnered.rows = body.rows ∧ partnered.reserve = body.reserve ∧
      partnered.components = [⟨0,.carbamoylPhosphate⟩] ∧
      let after := execute frame (Source.program frame partnered (actions ++ (Source.start frame next.previous).pending))
        (.joint partnered :: surplus)
      next.current.stock = after.stock ∧
      next.current.stages = (Source.start frame next.previous).stages ++
        [{after with fired := .attach initial .carbamoylPhosphate :: after.fired}] ∧
      next.current.captureRemaining = [] ∧ next.current.cut = after.missing := by
  rcases Birth.actual_live_body edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated oldActions with
    ⟨frame,previous,body,actual,held,_,_⟩
  rcases BathAccounting.actual_current_CP_present edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw
    depth generated oldActions with ⟨cpFrame,cpPrevious,cpActual,present,_,_⟩
  have same : (⟨frame,previous⟩ : Σ frame : CPS1Recycling.Frame, CPS1AtomicDynamics.Source.Occurrence frame) =
      ⟨cpFrame,cpPrevious⟩ := Option.some.inj (actual.symm.trans cpActual)
  cases same
  rcases capture_head frame previous body held with ⟨initialSurplus,head,_⟩
  have captured := Actual.capture_live_body frame previous body held
  have cp := capture_cp_present frame previous body held present
  have paid := advance_partner frame (Source.start frame previous) (Joint.fromBody frame body)
    initialSurplus head captured.2.1 cp actions feed
  dsimp only at paid
  rcases paid with ⟨surplus,inventory,stock,stages,remaining,cut⟩
  let next : Source.Occurrence frame :=
    ⟨previous,Source.advance frame (Source.start frame previous) (Source.generatedPartnerProgram ++ actions) feed⟩
  have generatedActual : Source.generatedExecution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions actions feed = some ⟨frame,next⟩ := by
    simp only [Source.generatedExecution,Source.execution,actual]
    rfl
  exact ⟨frame,next,body,surplus,generatedActual,held,captured.2.2.2,inventory,
    rfl,rfl,rfl,rfl,stock,stages,remaining,cut⟩

end
end CPS1EnzymeBath.Partner
