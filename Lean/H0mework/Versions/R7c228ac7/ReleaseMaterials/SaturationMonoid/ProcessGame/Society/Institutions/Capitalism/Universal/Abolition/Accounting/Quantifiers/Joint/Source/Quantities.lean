import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint

open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Entitlement.Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- This readout consumes the already generated source census once. It does
not normalize each amount by rerunning the control detector. -/
theorem a_singleton_source_scope_retains_its_entire_original_quantity
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good))
    (scope : Entitlement.Duty.scope source = [key]) (total : ℚ)
    (original : ((Entitlement.Source.demands source).map Entitlement.Source.Demand.quantity).sum = total)
    (other : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    Entitlement.Duty.quantity source other = if other = key then total else 0 := by
  have located (demand : Entitlement.Source.Demand source) (member : demand ∈ Entitlement.Source.demands source) :
      Entitlement.Duty.demandKey source demand = key := by
    have inside : Entitlement.Duty.demandKey source demand ∈ Entitlement.Duty.scope source :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨demand,member,rfl⟩)
    rw [scope] at inside
    exact List.mem_singleton.mp inside
  unfold Entitlement.Duty.quantity
  by_cases same : other = key
  · subst other
    have full : (Entitlement.Source.demands source).filter
        (fun demand => Entitlement.Duty.demandKey source demand = key) = Entitlement.Source.demands source := by
      apply List.filter_eq_self.mpr
      intro demand member
      simp only [located demand member,decide_true]
    rw [full,if_pos rfl]
    exact original
  · have empty : (Entitlement.Source.demands source).filter
        (fun demand => Entitlement.Duty.demandKey source demand = other) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro demand member
      rw [located demand member]
      intro accepted
      exact same (of_decide_eq_true accepted).symm
    rw [empty,if_neg same]
    rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint
