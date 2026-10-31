import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Report

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

variable (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

def targetAt (event : ExactTemporalCausalRootEventAt current.native.full.root.toAuthoritativeRoot.toLedgerRoot current.native.visit) :
    SourceNativeSequentialActualActionTargetAt current.native.full.root current.native.visit event
      (current.native.full.entry current.native.visit.current) current.native.authority := by
  rw [event.eq_generated]
  let core := Factory.Direct.targetAt current.native.full current.native.visit current.native.sourceActual
    current.executionReader complete (current.native.full.entry current.native.visit.current) current.native.authority
      (current.native.full.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit current.native.visit)
  refine {core with
    targetRoot := root current
    firstSuccessor := first current
    canonical_targetNextVisit_eq := ?_
    Answer := current.native.actual.RawAnswer current.native.reader
    answer := current.native.actual.rawAnswer current.native.reader
    Receipt := fun answer => ULift.{3,0} (Report current answer)
    receipt := ⟨report current⟩ }
  exact Ingress.next_is_the_same_generated_successor (root current) (.finite (initial current)) (first current)

def program : SourceNativeSequentialActualActionProgramAt current.native.full.root current.native.visit
    (current.native.full.entry current.native.visit.current) current.native.authority where
  targetAt := targetAt current complete

def generated := (program current complete).generate
  (current.native.full.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.native.visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
