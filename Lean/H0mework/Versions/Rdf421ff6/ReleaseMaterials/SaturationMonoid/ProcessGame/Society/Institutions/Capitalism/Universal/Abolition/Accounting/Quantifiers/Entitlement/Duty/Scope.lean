import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Demand

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty

open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev Key := Party × Party × Good

def demandKey (demand : Source.Demand window) : Key (Party := Party) (Good := Good) :=
  (demand.leg.sender,demand.leg.recipient,demand.leg.good)

def scope : List (Key (Party := Party) (Good := Good)) :=
  ((Source.demands window).map (demandKey window)).dedup

def quantity (key : Key (Party := Party) (Good := Good)) : ℚ :=
  ((Source.demands window).filter (fun demand => demandKey window demand = key) |>.map Source.Demand.quantity).sum

private theorem positive_sum (demands : List (Source.Demand window))
    (demand : Source.Demand window) (member : demand ∈ demands) :
    0 < (demands.map Source.Demand.quantity).sum := by
  induction demands with
  | nil => cases member
  | cons first rest inherited =>
      simp only [List.mem_cons] at member
      simp only [List.map_cons,List.sum_cons]
      have nonnegative : 0 ≤ (rest.map Source.Demand.quantity).sum := by
        apply List.sum_nonneg
        intro amount listed
        obtain ⟨item,_,rfl⟩ := List.mem_map.mp listed
        exact item.leg.quantity_positive.le
      cases member with
      | inl same => subst demand; exact add_pos_of_pos_of_nonneg first.leg.quantity_positive nonnegative
      | inr later => exact add_pos_of_nonneg_of_pos first.leg.quantity_positive.le (inherited later)

theorem every_group_retains_an_original_positive_bearer (key : Key (Party := Party) (Good := Good))
    (member : key ∈ scope window) : 0 < quantity window key := by
  obtain ⟨demand,original,same⟩ := List.mem_map.mp (List.mem_dedup.mp member)
  unfold quantity
  apply positive_sum window _ demand
  exact List.mem_filter.mpr ⟨original,by simp only [same,decide_true]⟩

theorem the_original_claim_has_a_positive_group (claim : Source.Claim window) :
    ∃ key ∈ scope window, 0 < quantity window key := by
  obtain ⟨demand,original,_⟩ := Source.a_claim_does_not_take_a_caller_quantity window claim
  have member : demandKey window demand ∈ scope window :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨demand,original,rfl⟩)
  exact ⟨_,member,every_group_retains_an_original_positive_bearer window _ member⟩

theorem every_group_is_enumerated_once : (scope window).Nodup := List.nodup_dedup _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty
