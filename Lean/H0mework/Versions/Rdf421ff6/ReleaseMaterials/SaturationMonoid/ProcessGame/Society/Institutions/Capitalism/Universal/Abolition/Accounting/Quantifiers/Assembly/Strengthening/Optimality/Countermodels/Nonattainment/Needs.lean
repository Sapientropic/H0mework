import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

theorem the_original_positive_living_and_maintenance_prefix_meets_all_source_needs :
    Exit.Necessity.AllNeedsPaid law initial [false,true] prefixWord := by decide +kernel

theorem appending_a_real_future_does_not_erase_any_original_need_payment
    (suffix : RawEvent Bool Bool Unit Nat Unit) :
    Exit.Necessity.AllNeedsPaid law initial [false,true] (prefixWord ++ suffix) := by
  have inventory : law.rawItems initial (prefixWord ++ suffix) = law.rawItems initial prefixWord ++
      (law.execute (law.execute initial 0 prefixWord).final prefixWord.length suffix).items := by
    unfold RawLaw.rawItems
    rw [RawLaw.execute_append]
    simp only [Nat.zero_add]
  intro actor present
  have paid := the_original_positive_living_and_maintenance_prefix_meets_all_source_needs actor present
  constructor
  · rcases paid.1 with empty | ⟨item,listed,accepted,matched⟩
    · exact Or.inl empty
    · exact Or.inr ⟨item,by rw [inventory]; exact List.mem_append_left _ listed,accepted,matched⟩
  · rcases paid.2 with empty | ⟨item,listed,accepted,matched⟩
    · exact Or.inl empty
    · exact Or.inr ⟨item,by rw [inventory]; exact List.mem_append_left _ listed,accepted,matched⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
