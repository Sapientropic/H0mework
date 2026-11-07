import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.Accounting
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.NativeFrame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace FinancialData

private theorem base_next_support
    (current : Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) :
    (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).support
      ((Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).account
        ((Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).next current))
      ⟨(Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).native current⟩ =
      (Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).sourceSupport
        ((Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).next current) := by
  have atTarget (target : Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      (same : target = Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
      (native : Epoch.Finance.Future.Continuation.NativeTail input depth count current.account target.account) :
      (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).support target.account native =
        Accounting.supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition target := by
    subst target
    exact same_source_step_reads_the_literal_next_support (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  exact atTarget _ (Accounting.successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) _

def base : FinancialData
    (Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) where
  Ready := fun current => Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = true
  ready_next := fun current _ => by
    exact (congrArg (Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      (Accounting.successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)).trans
      (Accounting.every_generated_next_has_a_completed_body (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
  bodyPaid := fun _ ready => ready
  familyAt := fun current ready =>
    ⟨accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current,
      (completed_body_uses_the_literal_existing_financial_world (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current ready).2.2⟩
  next_support := fun current _ => base_next_support current
  occurrence_eq_emitted := fun _ occurrence => Accounting.occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition occurrence

theorem base_first_body_is_ready :
    (base (input := input) (depth := depth) (count := count) (prefixLimit := prefixLimit)
      (renewalLimit := renewalLimit) (sourceDepth := sourceDepth) (sourceCount := sourceCount)
      (start := start) (proposal := proposal) (sourcePosition := sourcePosition)).Ready
      ((Accounting.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).next
        (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)) :=
  (congrArg (Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (Accounting.successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition))).trans
    (Accounting.every_generated_next_has_a_completed_body (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition _)

variable {frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}
  (data : FinancialData frame) {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

private def BornReady (current : Admission.Current frame registered) : Prop :=
  data.Ready current.1 ∧ match current.2 with
    | .pending => False
    | .registered _ => True

private def bornFamily (current : Admission.Current frame registered) (ready : BornReady data registered current) :
    { family : Epoch.Finance.Future.Continuation.AccountFamily input depth count
        (Admission.nativeFrame frame registered).N ((Admission.nativeFrame frame registered).account current) //
      family.currentSupport = (Admission.nativeFrame frame registered).sourceSupport current } := by
  rcases current with ⟨current, event⟩
  cases event with
  | pending => exact ready.2.elim
  | registered native =>
      let old := data.familyAt current ready.1
      refine ⟨Epoch.Finance.Future.Continuation.registeredFamily old.val (frame.account origin) (.inr registered.issued.claim) native, ?_⟩
      exact congrArg (fun support => (support, some (Admission.state frame registered (.registered native)))) old.property

private theorem born_next_support (current : Admission.Current frame registered) (ready : BornReady data registered current) :
    (bornFamily data registered current ready).val.support
      ((Admission.nativeFrame frame registered).account ((Admission.nativeFrame frame registered).next current))
      ⟨(Admission.nativeFrame frame registered).native current⟩ =
      (Admission.nativeFrame frame registered).sourceSupport ((Admission.nativeFrame frame registered).next current) := by
  rcases current with ⟨current, event⟩
  cases event with
  | pending => exact ready.2.elim
  | registered native =>
      have atTarget (target : Admission.Current frame registered)
          (same : target = Admission.next frame registered ⟨current, .registered native⟩)
          (step : Epoch.Finance.Future.Continuation.NativeTail input depth count (frame.account current) (frame.account target.1)) :
          (bornFamily data registered ⟨current, .registered native⟩ ready).val.support (frame.account target.1) step =
            Admission.supportAt frame registered target := by
        subst target
        apply Prod.ext
        · exact data.next_support current ready.1
        · rfl
      exact atTarget _ (Admission.successor_current frame registered ⟨current, .registered native⟩) _

def born : FinancialData (Admission.nativeFrame frame registered) where
  Ready := BornReady data registered
  ready_next := fun current ready => by
    have nextReady : BornReady data registered (Admission.next frame registered current) := by
      rcases current with ⟨current, event⟩
      cases event with
      | pending => exact ready.2.elim
      | registered native => exact ⟨data.ready_next current ready.1, trivial⟩
    exact Eq.mpr (congrArg (BornReady data registered) (Admission.successor_current frame registered current)) nextReady
  bodyPaid := fun current ready => data.bodyPaid current.1 ready.1
  familyAt := bornFamily data registered
  next_support := born_next_support data registered
  occurrence_eq_emitted := fun _ occurrence => Admission.occurrence_eq_emitted frame registered occurrence

theorem born_first_registration_is_ready (ready : data.Ready origin) :
    (data.born registered).Ready
      ((Admission.nativeFrame frame registered).next (Admission.initial frame registered)) := by
  have nextReady : BornReady data registered (Admission.next frame registered (Admission.initial frame registered)) :=
    ⟨data.ready_next origin ready, trivial⟩
  exact Eq.mpr (congrArg (BornReady data registered)
    (Admission.successor_current frame registered (Admission.initial frame registered))) nextReady

end FinancialData

#print axioms FinancialData.born
#print axioms FinancialData.base_first_body_is_ready
#print axioms FinancialData.born_first_registration_is_ready

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation
