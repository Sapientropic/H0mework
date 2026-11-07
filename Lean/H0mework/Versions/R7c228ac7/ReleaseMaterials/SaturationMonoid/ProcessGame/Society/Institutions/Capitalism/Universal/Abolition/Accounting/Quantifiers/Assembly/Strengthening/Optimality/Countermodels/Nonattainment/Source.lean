import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Execution
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def epsilon (n : Nat) : ℚ := 1 / ((n : ℚ) + 2)

theorem epsilon_positive (n : Nat) : 0 < epsilon n := by unfold epsilon; positivity

theorem epsilon_at_most_half (n : Nat) : epsilon n ≤ 1 / 2 := by
  unfold epsilon
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℚ) < 2)).2
  norm_num

def indexFor (tolerance : ℚ) : Nat := Nat.ceil (1 / tolerance)

theorem generated_index_improves_any_positive_gap (tolerance : ℚ) (positive : 0 < tolerance) :
    epsilon (indexFor tolerance) < tolerance := by
  have bound : 1 / tolerance ≤ (indexFor tolerance : ℚ) := Nat.le_ceil _
  have strict : 1 / tolerance < (indexFor tolerance : ℚ) + 2 := by linarith
  have paid : 1 < ((indexFor tolerance : ℚ) + 2) * tolerance := (div_lt_iff₀ positive).mp strict
  exact (div_lt_iff₀ (by positivity : (0 : ℚ) < (indexFor tolerance : ℚ) + 2)).mpr (by nlinarith)

def law : RawLaw Bool Bool Unit Nat Unit where
  technique := fun n actor => if actor then ⟨[],[],[],[]⟩ else
    ⟨[(true,epsilon n)],[(false,1)],[(true,1)],[]⟩
  controller := fun _ _ => true
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => false
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ actor => if actor then [] else [(false,1)]
  mandatoryMaintenance := fun _ actor => if actor then [] else [(true,1)]
  duration := fun _ => 0

def initial : RawCurrent Bool Bool Nat Unit where
  stock := fun actor good => if good then if actor then 0 else 6 else if actor then 1 else 0
  claims := fun _ _ _ => 0
  technology := 0
  clock := 0
  round := 0

def input : ProgrammeSource.Input Bool Bool Unit Nat Unit := {law := law,initial := initial,instructions := []}
def request (actor : Bool) (operation : Operation Bool Bool Nat Unit) : Request Bool Bool Unit Nat Unit :=
  ⟨actor,[],(),[],operation⟩
def issued := request false (.issue () false true 1)
def advance := request true (.transfer true false [(false,1)])
def living := request false (.use false [(false,1)] .necessity)
def maintain := request false (.use false [(true,1)] .maintenance)
def prefixWord := [issued,advance,living,maintain]
def initialHistory := prefixWord.map Compile.RawInput.primitive

def genesis := Physical.Public.stateAt input 0 0 0 0 [] []
def before := Programme.run input genesis initialHistory

def reading : Cost.LinearReadout Bool Bool where
  resourceWeight := fun _ _ good => if good then 1 else 0
  resource_nonnegative := by intro _ _ good; cases good <;> norm_num
  timeWeight := 0
  time_nonnegative := by norm_num

def fullReading : Cost.LinearReadout Bool Bool where
  resourceWeight := fun _ _ _ => 1
  resource_nonnegative := by intro _ _ _; norm_num
  timeWeight := 1
  time_nonnegative := by norm_num

theorem the_active_physical_interpreter_is_the_same_source_law : Physical.Public.interpreter input = law := rfl

attribute [local simp] epsilon request
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
