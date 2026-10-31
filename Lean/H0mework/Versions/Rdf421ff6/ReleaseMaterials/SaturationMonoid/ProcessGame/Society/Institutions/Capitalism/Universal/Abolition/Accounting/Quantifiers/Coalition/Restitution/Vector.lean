import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Read
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.Scope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]

/-- The two original bearers of one control transfer, in its original unit. -/
def incidence (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    ℚ →+ Profit.Vector (Party := Party) (Good := Good) :=
  Finsupp.singleAddHom (key.2.1,key.2.2) - Finsupp.singleAddHom (key.1,key.2.2)

/-- A finite restriction of the source matrix, not another responsibility ledger. -/
def position (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (amounts : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ) :
    Profit.Vector (Party := Party) (Good := Good) :=
  (scope.map fun key => incidence key (amounts key)).sum

omit [DecidableEq Party] [DecidableEq Good] in
theorem position_add (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (left right : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ) :
    position scope (fun key => left key + right key) = position scope left + position scope right := by
  simp only [position,map_add,List.sum_map_add]

omit [DecidableEq Party] [DecidableEq Good] in
theorem position_zero (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good))) :
    position scope (fun _ => 0) = 0 := by simp [position]

omit [DecidableEq Party] [DecidableEq Good] in
theorem incidence_keeps_the_original_two_bearers
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) (quantity : ℚ) :
    incidence key quantity = Finsupp.single (key.2.1,key.2.2) quantity -
      Finsupp.single (key.1,key.2.2) quantity := rfl

omit [DecidableEq Party] in
theorem every_coalition_reads_the_same_original_unit
    (members : Party → Bool) (good : Good)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) (quantity : ℚ) :
    read members good (incidence key quantity) =
      (if members key.2.1 = true ∧ key.2.2 = good then quantity else 0) -
        (if members key.1 = true ∧ key.2.2 = good then quantity else 0) := by
  rw [incidence_keeps_the_original_two_bearers,map_sub,read_single,read_single]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution
