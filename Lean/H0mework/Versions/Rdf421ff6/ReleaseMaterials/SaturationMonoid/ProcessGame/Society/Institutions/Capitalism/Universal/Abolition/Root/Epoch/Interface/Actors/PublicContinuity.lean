import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Registered.Compile.RawInput Party Good Port Technology Instrument))
  (current : Registered.Physical.Cursor Party Good Port Technology Instrument)

theorem the_public_prelude_keeps_the_literal_existing_location
    (party : Party) (location : Location input depth count)
    (original : prelude input depth count
      (.actual prefixLimit renewalLimit (Registered.Physical.Prefix.cursor oldPast)) party = some location) :
    prelude input depth count (.publicActual prefixLimit renewalLimit oldPast current) party = some location := by
  unfold prelude at original ⊢
  cases found : Epoch.Actors.oldLookup input depth count party with
  | some witness => simpa only [found] using original
  | none =>
      simp only [found] at original ⊢
      rw [Registered.Physical.Prefix.past_readback] at original
      rw [original]
      rfl

theorem the_public_root_inherits_the_same_M0_image
    (party : Party) (location : Location input depth count)
    (original : prelude input depth count
      (.actual prefixLimit renewalLimit (Registered.Physical.Prefix.cursor oldPast)) party = some location) :
    lookup input depth count (.publicActual prefixLimit renewalLimit oldPast current)
        (root input depth count (.publicActual prefixLimit renewalLimit oldPast current)).initialVisit party = some location ∧
      (lookup input depth count (.publicActual prefixLimit renewalLimit oldPast current)
        (root input depth count (.publicActual prefixLimit renewalLimit oldPast current)).initialVisit party).map
          (Location.actor input depth count) = some (location.actor input depth count) := by
  have kept : lookup input depth count (.publicActual prefixLimit renewalLimit oldPast current)
      (root input depth count (.publicActual prefixLimit renewalLimit oldPast current)).initialVisit party = some location := by
    change (prelude input depth count (.publicActual prefixLimit renewalLimit oldPast current) party).orElse _ = _
    rw [the_public_prelude_keeps_the_literal_existing_location input depth count prefixLimit renewalLimit oldPast current party location original]
    rfl
  exact ⟨kept, congrArg (Option.map (Location.actor input depth count)) kept⟩

#print axioms the_public_prelude_keeps_the_literal_existing_location
#print axioms the_public_root_inherits_the_same_M0_image

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors
