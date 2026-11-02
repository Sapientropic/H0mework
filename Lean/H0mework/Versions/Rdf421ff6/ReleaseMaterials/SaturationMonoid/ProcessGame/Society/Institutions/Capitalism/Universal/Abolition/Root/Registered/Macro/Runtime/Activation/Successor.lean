import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Raw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (review : Option (ReviewPhase.ContextAt input))

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount review}

namespace ActivatedFrame

variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

theorem successor_valid (query : frame.presentation.Query) :
    frame.next.presentation.erase = (RootInquiryProcessNode.answered frame.presentation query).erase ∧
      (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
        query (.active frame.next.presentation) := by
  have same := frame.query_unique query
  cases same
  cases frame with
  | enacted origin admission current => exact current.successor_valid current.query
  | original current =>
      cases selected : current.query with
      | internal work =>
          dsimp only [next]
          rw [selected]
          dsimp only [Frame.nextAt, Frame.internalNext]
          cases found : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
              current.start current.proposal current.sourcePosition current.package.frame current.visit.current with
          | none => simpa only [presentation, query, selected, Frame.controlledPresentation] using current.ordinary_controlled_successor_valid work found
          | some registered => simpa only [presentation, query, selected, Frame.controlledPresentation] using current.born_controlled_successor_valid work registered found
      | raw germ =>
          dsimp only [next]
          rw [selected]
          dsimp only
          cases chosen : Abolition.Functions.Revision.InitialAdmission.select (current.controlOrigin germ) with
          | admitted admission => simpa only [presentation, query, selected, Frame.controlledPresentation] using current.enactment_controlled_successor_valid germ admission chosen
          | obstructed failed => simpa only [presentation, query, selected, Frame.controlledPresentation, Frame.nextAt] using current.raw_controlled_successor_valid germ failed chosen

end ActivatedFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
