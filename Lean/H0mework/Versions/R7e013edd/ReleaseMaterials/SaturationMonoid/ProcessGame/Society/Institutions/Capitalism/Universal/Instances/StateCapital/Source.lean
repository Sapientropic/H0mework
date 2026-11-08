import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Retiming
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Reserve

/-! An institutional productive controller pays wages and mandatory upkeep,
then invests real material in a technology change.  The improved technique
generates a larger surplus on subsequent executions.  Raw party keys acquire
their actor lineages through the common source compiler. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.StateCapital

open Source.Program

abbrev Current := RawCurrent Bool Bool Bool Unit
abbrev Input := Request Bool Bool Bool Bool Unit

def material : Bool := true
def labour : Bool := false

def law : RawLaw Bool Bool Bool Bool Unit where
  technique := fun improved worker => if worker then
    ⟨[(material, 1)], [(labour, 1)], [], [true]⟩ else
    ⟨[(material, 1), (labour, 1)], [(material, if improved then 6 else 5)], [], [false]⟩
  controller := fun _ port => port
  allowed := fun _ port signer => decide (port = signer)
  stockPort := fun _ holder _ => holder
  revisionPort := fun _ => false
  revisionCost := fun old new => if old = new then [] else [(material, 1)]
  settlementUnit := fun _ => material
  settlementRate := fun _ => 1
  issuerPort := fun _ => false
  necessities := fun _ worker => if worker then [(material, 1)] else []
  mandatoryMaintenance := fun _ worker => if worker then [] else [(material, 1)]
  duration := fun _ => 1

theorem time_independent : law.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem reserve_insensitive : law.ReserveInsensitive :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def state (clock : ℚ) (round : Nat) (improved : Bool) (accumulated : ℚ) : Current where
  stock := fun worker good => if good then 1 + if worker then 0 else accumulated else 0
  claims := fun _ _ _ => 0
  technology := improved
  clock := clock
  round := round

def reproduceLabour : Input := ⟨true, [], true, [], .produce true⟩
def contribute : Input := ⟨true, [], false, [], .transfer true false [(labour, 1)]⟩
def produce : Input := ⟨false, [], false, [], .produce false⟩
def wage : Input := ⟨false, [], false, [], .transfer false true [(material, 2)]⟩
def consume : Input := ⟨true, [], true, [], .use true [(material, 1)] .necessity⟩
def maintain : Input := ⟨false, [], false, [], .use false [(material, 1)] .maintenance⟩
def invest : Input := ⟨false, [], false, [], .revise false true⟩

def body : List Input := [reproduceLabour, contribute, produce, wage, consume, maintain, invest]
def program : RawProgram Bool Bool Bool Bool Unit := ⟨law, state 0 0 false 0, fun _ => body⟩

theorem productive_capacity_actually_changes :
    (law.technique false false).outputs = [(material, 5)] ∧
    (law.technique true false).outputs = [(material, 6)] := ⟨rfl, rfl⟩

theorem investment_has_real_material_cost : law.revisionCost false true = [(material, 1)] := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.StateCapital
