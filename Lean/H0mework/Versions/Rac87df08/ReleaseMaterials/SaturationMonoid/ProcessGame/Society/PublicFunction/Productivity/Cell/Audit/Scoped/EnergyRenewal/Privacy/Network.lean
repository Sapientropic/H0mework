import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network
open Lean

/-- A channel gets public input, the complete source result, and exogenous input.
The latter includes actual clocks, scheduling, identities, entropy and cryptographic execution.
No timestamp, error, signature or visible byte is projected away from Observation. -/
structure Channel (State Noise Observation : Type) where
  step : State → Json → Except String Json → Noise → State × Observation

def run {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (larger : Bool) (initial : State) (strategy : List Observation → Nat → Json) (tape : Nat → Noise) :
    Nat → State × List Observation
  | 0 => (initial,[])
  | n+1 =>
    let (state,past) := run channel larger initial strategy tape n
    let request := strategy past n
    let (next,observation) := channel.step state request (Wire.actual larger request) (tape n)
    (next,past ++ [observation])

/-- Shared-tape coupling is a proof technique; actual independent executions need not have equal random bytes or clocks. -/
theorem full_observation_coupling {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (initial : State) (strategy : List Observation → Nat → Json) (tape : Nat → Noise) (count : Nat) :
    run channel false initial strategy tape count = run channel true initial strategy tape count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [run,ih,Wire.actual_branches_equal]

/-- Executed public readout uses the same kernel, with no private selector on its path. -/
def publicRun {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (initial : State) (strategy : List Observation → Nat → Json) (tape : Nat → Noise) :
    Nat → State × List Observation
  | 0 => (initial,[])
  | n+1 =>
    let (state,past) := publicRun channel initial strategy tape n
    let request := strategy past n
    let (next,observation) := channel.step state request (Wire.publicReadout request) (tape n)
    (next,past ++ [observation])

theorem public_run_is_actual {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (larger : Bool) (initial : State) (strategy : List Observation → Nat → Json) (tape : Nat → Noise) (count : Nat) :
    publicRun channel initial strategy tape count = run channel larger initial strategy tape count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [publicRun,run,ih,Wire.public_readout_is_actual larger]

/-- A finite-prefix law retains the full observation and its weight. Every finite random-bit law is admitted. -/
def observationLaw {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (larger : Bool) (initial : State) (strategy : List Observation → Nat → Json)
    (law : List ((Nat → Noise) × ℚ)) (count : Nat) : List ((State × List Observation) × ℚ) :=
  law.map fun (tape,weight) => (run channel larger initial strategy tape count,weight)

/-- The tape law is fixed outside the private source. It includes scheduler/clock laws;
this theorem does not assert that an arbitrary operating system supplies such independence. -/
theorem all_exogenous_laws_preserve_complete_observation_distribution {State Noise Observation : Type}
    (channel : Channel State Noise Observation) (initial : State) (strategy : List Observation → Nat → Json)
    (law : List ((Nat → Noise) × ℚ)) (count : Nat) :
    observationLaw channel false initial strategy law count = observationLaw channel true initial strategy law count := by
  unfold observationLaw
  congr 1
  funext item
  rcases item with ⟨tape,weight⟩
  dsimp only
  rw [full_observation_coupling]

/-- Both independent draws use their own tape; the joint law is the product of the common marginal. -/
def independentLaw {State Noise Observation : Type} (channel : Channel State Noise Observation)
    (leftLarger rightLarger : Bool) (initial : State) (strategy : List Observation → Nat → Json)
    (law : List ((Nat → Noise) × ℚ)) (count : Nat) :=
  law.flatMap fun (left,lw) => law.map fun (right,rw) =>
    ((run channel leftLarger initial strategy left count,run channel rightLarger initial strategy right count),lw*rw)

theorem independent_draws_have_the_same_product_law {State Noise Observation : Type}
    (channel : Channel State Noise Observation) (initial : State) (strategy : List Observation → Nat → Json)
    (law : List ((Nat → Noise) × ℚ)) (count : Nat) :
    independentLaw channel false true initial strategy law count = independentLaw channel false false initial strategy law count := by
  unfold independentLaw
  congr 1
  funext left
  rcases left with ⟨left,lw⟩
  dsimp only
  congr 1
  funext right
  rcases right with ⟨right,rw⟩
  dsimp only
  simp only [full_observation_coupling]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network
