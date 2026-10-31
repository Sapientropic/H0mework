import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Original

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Entitlement.Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Source legs outside the actual Demand classifier remain in a separate
restriction. Absence from this classifier is not a new legitimacy judgment. -/
def retainedLeg (leg : window.Leg) : Profit.Vector (Party := Party) (Good := Good) :=
  match Entitlement.Source.readDemand window leg with
  | some _ => 0
  | none => originalLeg window leg

def retainedOriginalLegs : Profit.Vector (Party := Party) (Good := Good) :=
  (window.legs.map (retainedLeg window)).sum

private theorem partition (legs : List window.Leg) :
    (legs.map (originalLeg window)).sum =
      ((legs.filterMap (Entitlement.Source.readDemand window)).map fun demand => originalLeg window demand.leg).sum +
        (legs.map (retainedLeg window)).sum := by
  induction legs with
  | nil => simp
  | cons leg rest inherited =>
      cases source : Entitlement.Source.readDemand window leg with
      | none =>
          simp only [List.map_cons,List.sum_cons,List.filterMap_cons,source,retainedLeg] at inherited ⊢
          rw [inherited]
          abel
      | some demand =>
          have same := reading_a_source_demand_keeps_its_actual_leg window leg demand source
          simp only [List.map_cons,List.sum_cons,List.filterMap_cons,source,retainedLeg,same] at inherited ⊢
          rw [inherited]
          abel

theorem source_classification_preserves_every_other_original_leg :
    (window.legs.map (originalLeg window)).sum = originalControl window + retainedOriginalLegs window :=
  partition window window.legs

theorem an_exercised_grant_is_retained_in_full
    (leg : window.Leg) (grant : Entitlement.Source.ExercisedGrant window leg) :
    retainedLeg window leg = originalLeg window leg := by
  unfold retainedLeg
  rw [an_exercised_original_grant_is_not_control_debt window leg grant]

theorem a_signed_gift_is_retained_in_full
    (leg : window.Leg) (signed : leg.item.val.request.signer = leg.sender) :
    retainedLeg window leg = originalLeg window leg :=
  an_exercised_grant_is_retained_in_full window leg (.sourceSignature signed)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution
