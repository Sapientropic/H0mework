import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedReactiveJoint.Particle
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Facts

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CPS1AddressedReactiveJoint.Rows
noncomputable section
open CPS1AddressedHydrolysis
abbrev Row := CPS1AtomicDynamics.Body.Row
abbrev Stock := List (Address × Row)

def row? (rows : Stock) (address : Address) : Option Row :=
  (rows.find? (fun item => item.1 = address)).map Prod.snd

def readoutRows (particles : List Particle) (rows : Stock) :
    List (CPS1AtomicDynamics.Charged.Address × Row) :=
  particles.filterMap (fun particle => (row? rows particle.address).map (fun row => (particle.readout.address,row)))

theorem readout_absent (particles : List Particle) (rows : Stock)
    (address : CPS1AtomicDynamics.Charged.Address)
    (absent : address ∉ particles.map (fun particle => particle.readout.address)) :
    CPS1AtomicDynamics.Body.row? (readoutRows particles rows) address = none := by
  induction particles with
  | nil => rfl
  | cons particle rest ih =>
    have different : particle.readout.address ≠ address := by
      intro same
      exact absent (List.mem_cons.mpr (Or.inl same.symm))
    have remainder : address ∉ rest.map (fun particle => particle.readout.address) := by
      intro member
      exact absent (List.mem_cons_of_mem _ member)
    cases known : row? rows particle.address with
    | none => simpa only [readoutRows,List.filterMap_cons,known,Option.map_none] using ih remainder
    | some row =>
      simpa only [readoutRows,List.filterMap_cons,known,Option.map_some,
        CPS1AtomicDynamics.Body.row?,List.find?_cons,decide_eq_false_iff_not.mpr different,Option.map_none] using ih remainder

theorem readout_row (particles : List Particle) (rows : Stock)
    (unique : (particles.map (fun particle => particle.readout.address)).Nodup)
    (particle : Particle) (member : particle ∈ particles) :
    CPS1AtomicDynamics.Body.row? (readoutRows particles rows) particle.readout.address =
      row? rows particle.address := by
  induction particles with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with selected | later
    · subst particle
      cases known : row? rows first.address with
      | none =>
        simpa only [readoutRows,List.filterMap_cons,known,Option.map_none] using
          readout_absent rest rows first.readout.address distinct.1
      | some row => simp [readoutRows,known,CPS1AtomicDynamics.Body.row?]
    · have different : first.readout.address ≠ particle.readout.address := by
        intro same
        apply distinct.1
        change first.readout.address ∈ _
        rw [same]
        exact List.mem_map.mpr ⟨particle,later,rfl⟩
      cases known : row? rows first.address with
      | none =>
        simpa only [readoutRows,List.filterMap_cons,known,Option.map_none] using ih distinct.2 later
      | some row =>
        simpa only [readoutRows,List.filterMap_cons,known,Option.map_some,
          CPS1AtomicDynamics.Body.row?,List.find?_cons,decide_eq_false_iff_not.mpr different,Option.map_none] using ih distinct.2 later

inductive Failure
  | unknownAddress (address : Address)
  | conflictingRow (address : Address)
  | nonpositiveInertia (address : Address)
  | negativeEnergy
  | repeatedOrigin
  | body (failure : CPS1AtomicDynamics.Body.Failure)
  deriving DecidableEq

structure State where
  rows : Stock
  reserve : ℝ

def report? (particles : List Particle) (state : State) (address : Address) (row : Row) :
    Except Failure State := by
  classical
  exact if !(particles.any (fun particle => particle.address = address)) then .error (.unknownAddress address)
    else if row.inertia ≤ 0 then .error (.nonpositiveInertia address)
    else match row? state.rows address with
    | some old => if old = row then .ok state else .error (.conflictingRow address)
    | none => .ok {state with rows := (address,row) :: state.rows}

def deposit? (state : State) (amount : ℝ) : Except Failure State :=
  if amount < 0 then .error .negativeEnergy else .ok {state with reserve := state.reserve+amount}

inductive RawAction
  | report (address : Address) (row : Row)
  | deposit (amount : ℝ)

def apply? (particles : List Particle) (state : State) : RawAction → Except Failure State
  | .report address row => report? particles state address row
  | .deposit amount => deposit? state amount

structure Execution where
  state : State
  paid : List RawAction
  pending : List RawAction
  cut : Option Failure

def run (particles : List Particle) (state : State) (actions : List RawAction) : Execution :=
  List.rec (motive := fun _ => State → Execution)
    (fun current => ⟨current,[],[],none⟩)
    (fun action rest recur current => match apply? particles current action with
      | .error failure => ⟨current,[],action :: rest,some failure⟩
      | .ok next => let tail := recur next
        ⟨tail.state,action :: tail.paid,tail.pending,tail.cut⟩) actions state

theorem run_nil (particles : List Particle) (state : State) : run particles state [] = ⟨state,[],[],none⟩ := rfl

theorem run_cons (particles : List Particle) (state : State) (action : RawAction) (rest : List RawAction) :
    run particles state (action :: rest) = match apply? particles state action with
      | .error failure => ⟨state,[],action :: rest,some failure⟩
      | .ok next => let tail := run particles next rest
        ⟨tail.state,action :: tail.paid,tail.pending,tail.cut⟩ := rfl

theorem run_whole (particles : List Particle) (state : State) (actions : List RawAction) :
    (run particles state actions).paid ++ (run particles state actions).pending = actions := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
    rw [run_cons]
    cases apply? particles state action with
    | error => rfl
    | ok next => exact congrArg (List.cons action) (ih next)

theorem report_generated (particles : List Particle) (state : State) (address : Address) (row : Row)
    (next : State) (actual : report? particles state address row = .ok next) :
    (∃ particle ∈ particles, particle.address = address) ∧ 0 < row.inertia ∧
      row? next.rows address = some row ∧ next.reserve = state.reserve ∧
      (∀ oldAddress oldRow, row? state.rows oldAddress = some oldRow → row? next.rows oldAddress = some oldRow) := by
  unfold report? at actual
  split at actual
  · cases actual
  · rename_i present
    have existsParticle : ∃ particle ∈ particles, particle.address = address := by
      have available : particles.any (fun particle => decide (particle.address = address)) = true := by
        simpa using present
      rcases List.any_eq_true.mp available with ⟨particle,member,same⟩
      exact ⟨particle,member,of_decide_eq_true same⟩
    split at actual
    · cases actual
    · rename_i positive
      cases prior : row? state.rows address with
      | some old =>
        simp only [prior] at actual
        split at actual
        · rename_i same
          cases Except.ok.inj actual
          exact ⟨existsParticle,lt_of_not_ge positive,same ▸ prior,rfl,fun _ _ held => held⟩
        · cases actual
      | none =>
        simp only [prior,Except.ok.injEq] at actual
        subst next
        refine ⟨existsParticle,lt_of_not_ge positive,?_,rfl,?_⟩
        · simp [row?]
        · intro oldAddress oldRow held
          have different : address ≠ oldAddress := by
            intro same
            rw [same] at prior
            rw [held] at prior
            cases prior
          simpa only [row?,List.find?_cons,decide_eq_false_iff_not.mpr different] using held

theorem apply_rows_preserved (particles : List Particle) (state next : State) (action : RawAction)
    (actual : apply? particles state action = .ok next) :
    ∀ address row, row? state.rows address = some row → row? next.rows address = some row := by
  cases action with
  | report address row => exact (report_generated particles state address row next actual).2.2.2.2
  | deposit amount =>
    change deposit? state amount = .ok next at actual
    unfold deposit? at actual
    split at actual
    · cases actual
    · cases Except.ok.inj actual
      exact fun _ _ held => held

theorem run_rows_preserved (particles : List Particle) (state : State) (actions : List RawAction) :
    ∀ address row, row? state.rows address = some row → row? (run particles state actions).state.rows address = some row := by
  induction actions generalizing state with
  | nil => exact fun _ _ held => held
  | cons action rest ih =>
    rw [run_cons]
    cases applied : apply? particles state action with
    | error => exact fun _ _ held => held
    | ok next =>
      intro address row held
      exact ih next address row (apply_rows_preserved particles state next action applied address row held)

def gather (atoms : List Atom) (rows : Stock) : Except Failure (List CPS1AtomicDynamics.Body.Node) :=
  if (atoms.map Atom.origin).Nodup then
    (CPS1AtomicDynamics.Body.gather ((particles atoms).map Particle.readout)
      (readoutRows (particles atoms) rows)).mapError Failure.body
  else .error .repeatedOrigin

theorem gather_generated (atoms : List Atom) (rows : Stock) (nodes : List CPS1AtomicDynamics.Body.Node)
    (actual : gather atoms rows = .ok nodes) :
    (atoms.map Atom.origin).Nodup ∧ nodes.map CPS1AtomicDynamics.Body.Node.particle =
      (particles atoms).map Particle.readout ∧
    (∀ node ∈ nodes, 0 < node.row.inertia ∧
      ∃ particle ∈ particles atoms, node.particle = particle.readout ∧ row? rows particle.address = some node.row) := by
  unfold gather at actual
  split at actual
  · rename_i unique
    cases gathered : CPS1AtomicDynamics.Body.gather ((particles atoms).map Particle.readout)
        (readoutRows (particles atoms) rows) with
    | error => simp only [gathered,Except.mapError] at actual; cases actual
    | ok result =>
      simp only [gathered,Except.mapError,Except.ok.injEq] at actual
      subst nodes
      have source := CPS1AtomicDynamics.Body.gather_source _ _ _ gathered
      refine ⟨unique,source.1,?_⟩
      intro node member
      have original := source.1 ▸ List.mem_map.mpr ⟨node,member,rfl⟩
      rcases List.mem_map.mp original with ⟨particle,held,identity⟩
      have row := (source.2 node member).2
      rw [← identity,readout_row _ rows (particle_readout_unique atoms) particle held] at row
      exact ⟨(source.2 node member).1,particle,held,identity.symm,row⟩
  · cases actual

end
end CPS1AddressedReactiveJoint.Rows
