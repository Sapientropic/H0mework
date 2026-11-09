import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue.Validity
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue.Read
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Head

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
noncomputable section
variable (current : NativeCurrent (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit))
  (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual)
  (selected : current.actual.proposal current.reader = .primitive request)

def body := current.raw complete

theorem checked : (Physical.Public.interpreter current.input).Valid
    (Public.Scope.actualState current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast current.actual.snapshot).raw request := valid_at_every_actual_raw _ _

def bodyItems := Public.Accounting.items (body current complete).input (body current complete).depth
  (body current complete).count (body current complete).prefixLimit (body current complete).renewalLimit
  (body current complete).oldPast (body current complete).start

include selected

theorem head : ∃ item, (bodyItems current complete) = [item] ∧ Public.Accounting.item? (body current complete).input (body current complete).depth (body current complete).count
    (body current complete).prefixLimit (body current complete).renewalLimit (body current complete).oldPast (body current complete).start (body current complete).actual.actual = some item :=
  Clearing.the_actual_primitive_has_its_own_financial_head current request
    selected complete rfl (checked current)

theorem each_item_is_the_actual_accepted_issue (item : Epoch.Finance.ActualItem current.input current.depth current.count)
    (listed : item ∈ (bodyItems current complete)) :
    (item.instruction current.input current.depth current.count).request = request ∧
      (item.interpreter current.input current.depth current.count).Valid
        (item.instruction current.input current.depth current.count).before
        (item.instruction current.input current.depth current.count).request := by
  have mapped := Clearing.the_actual_raw_owns_its_one_original_native_item current request
    selected complete rfl (checked current)
  have member : item.instruction current.input current.depth current.count ∈
      (bodyItems current complete).map (Epoch.Finance.ActualItem.instruction current.input current.depth current.count) :=
    List.mem_map.mpr ⟨item,listed,rfl⟩
  change item.instruction current.input current.depth current.count ∈
    (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast (Evolution.Factory.Direct.selectedStart current.full current.sourceActual current.reader)).map _ at member
  change (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast (Evolution.Factory.Direct.selectedStart current.full current.sourceActual current.reader)).map _ = _ at mapped
  rw [mapped] at member
  have exactItem := List.mem_singleton.mp member
  refine ⟨congrArg ExecutionItem.request exactItem,?_⟩
  have sameLaw : item.interpreter current.input current.depth current.count = Physical.Public.interpreter current.input := by
    change item ∈ Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast (Evolution.Factory.Direct.selectedStart current.full current.sourceActual current.reader) at listed
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp listed
    rfl
  rw [sameLaw,exactItem]
  exact checked current

theorem found : (Public.Accounting.registration? (body current complete).input (body current complete).depth (body current complete).count (body current complete).prefixLimit
    (body current complete).renewalLimit (body current complete).oldPast (body current complete).start (body current complete).actual.actual).isSome = true := by
  obtain ⟨item,single,present⟩ := head current complete selected
  have listed : item ∈ (bodyItems current complete) := by rw [single]; exact List.mem_singleton_self _
  obtain ⟨sameRequest,valid⟩ := each_item_is_the_actual_accepted_issue current complete selected item listed
  have operation : (item.instruction current.input current.depth current.count).request.operation = .issue () false true 1 :=
    congrArg Request.operation sameRequest
  have hasClaim := an_actual_accepted_issue_generates_its_original_native_claim current.input current.depth current.count
    item operation valid
  unfold Public.Accounting.registration?
  rw [dif_pos (body current complete).bodyPaid]
  split
  · rename_i absent
    cases absent.symm.trans present
  · rename_i chosen foundHead
    cases Option.some.inj (foundHead.symm.trans present)
    split
    · rename_i noClaim
      change Epoch.Finance.readNewClaim current.input current.depth current.count item = none at noClaim
      rw [noClaim] at hasClaim
      cases hasClaim
    · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue.Native
