import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Law

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program Capitalism.Universal.Abolition.Accounting.Quantifiers
open Capitalism.Universal.Abolition.Accounting
open Capitalism.Universal.Abolition.Innovation
open SaturationMonoid.ProcessGame.Society.PublicFunction
open PublicFunction.Mandate
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

namespace Compact
export Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
  (law)
end Compact

inductive Port where
  | ordinary (old : Bool)
  | service
  | challenge
  deriving DecidableEq

abbrev Tech := State Bool Unit
abbrev Raw := RawCurrent Bool Bool Tech Unit
abbrev Req := Request Bool Bool Port Tech Unit

def base : RawLaw Bool Bool Port Unit Unit where
  technique := fun technology actor =>
    let old := Compact.law.technique technology actor
    ⟨old.inputs, old.outputs, old.maintenance, old.requiredPorts.map .ordinary⟩
  controller := fun _ _ => true
  allowed := fun technology port actor => match port with
    | .ordinary old => Compact.law.allowed technology old actor
    | _ => false
  stockPort := fun _ _ _ => .ordinary false
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => []
  settlementUnit := Compact.law.settlementUnit
  settlementRate := Compact.law.settlementRate
  issuerPort := fun _ => .ordinary false
  necessities := Compact.law.necessities
  mandatoryMaintenance := Compact.law.mandatoryMaintenance
  duration := Compact.law.duration

def scope : Scope (Party := Bool) (Good := Bool) (Port := Port) :=
  ⟨⟨[⟨false, [(true, 1)], .maintenance⟩], 0, 20, by decide +kernel⟩, .service, .challenge, by decide, []⟩

abbrev active := Mandate.law base scope

def releasedTech : Tech := ⟨(), 0, none, none, none⟩

def liftOperation : Operation Bool Bool Unit Unit → Operation Bool Bool Tech Unit
  | .produce actor => .produce actor
  | .transfer sender recipient goods => .transfer sender recipient goods
  | .use person goods purpose => .use person goods purpose
  | .issue instrument debtor creditor quantity => .issue instrument debtor creditor quantity
  | .assign instrument debtor creditor replacement quantity => .assign instrument debtor creditor replacement quantity
  | .settle instrument debtor creditor quantity => .settle instrument debtor creditor quantity
  | .revise actor _ => .revise actor releasedTech
  | .present => .present

def liftRequest (old : Request Bool Bool Bool Unit Unit) : Req :=
  ⟨old.signer, old.consents, .ordinary old.purpose, old.gates.map .ordinary, liftOperation old.operation⟩

def initial : Raw :=
  let old := Entitlement.Consumer.initial
  ⟨old.stock, old.claims, releasedTech, old.clock, old.round⟩

def before := active.next initial []
def nature : Req := ⟨false, [], .ordinary false, [], .produce false⟩

abbrev code : Distributed.Code Bool Bool Port Tech Unit where
  law := active
  initial := before
  task := ⟨[⟨false, [(true, 1)], .necessity⟩], 0, 10, by decide +kernel⟩
  actions := []
  actionLimit := 0
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.adversary nature]
  eventLimit := 1
  eligible := fun _ => true
  parties := [false, true]
  goods := [false, true]
  instruments := [()]
  parties_cover := by intro actor; cases actor <;> simp
  goods_cover := by intro good; cases good <;> simp
  instruments_cover := by intro instrument; cases instrument; simp

def mechanism : Trials.Mechanism Bool Bool Port Tech Unit where
  code := code
  policy := fun _ _ => []
  terms := ⟨false, true, (), 1⟩
  funding := [Entitlement.Consumer.issued, Entitlement.Consumer.advanced, Entitlement.Consumer.need,
    Entitlement.Consumer.taking, Entitlement.Consumer.retained].map liftRequest
  investment := [(true, 1)]
  investmentPort := .ordinary false
  probe := []
  observer := 0
  closing := []

def past : List (List Req) := [[]]
def response : Control.HistoryResponse (Party := Bool) (Good := Bool) (Port := Port)
    (Technology := Tech) (Instrument := Unit) := fun _ _ _ => []
def originalWord := Control.responseWord mechanism past nature response

def input : ProgrammeSource.Input Bool Bool Port Tech Unit where
  law := active
  initial := initial
  instructions := originalWord

theorem productive_gap :
    Responsibility.partyLoss mechanism past nature response false false = 18 ∧
      Responsibility.controllerCohort mechanism past nature response = [true] := by decide +kernel

def productiveClaim : Responsibility.Family.Claim mechanism past nature response :=
  (Responsibility.Family.assess mechanism past nature response).get (by
    have positive : 0 < Responsibility.partyLoss mechanism past nature response false false := by
      rw [productive_gap.1]
      norm_num
    have member := Responsibility.Family.every_positive_original_harm_is_in_the_generated_scope
      mechanism past nature response false false positive
    have nonempty : Responsibility.Family.positiveScope mechanism past nature response ≠ [] := by
      intro empty
      rw [empty] at member
      exact List.not_mem_nil member
    simp [Responsibility.Family.assess, nonempty])

def original := Financial.Installation.Runtime.frames input 0 19
def native := original.native
def visit : SourceNativeTemporalVisitAt native.root.toAuthoritativeRoot.toLedgerRoot := original.temporal input

theorem cursor_eq : original.cursor input = Financial.Installation.Runtime.cursorAt input 0 19 :=
  Financial.Installation.Runtime.frames_cursor input 0 19

theorem consumed :
    Financial.Installation.Cursor.lastExecutedIndex input (Financial.Installation.Runtime.cursorAt input 0 19) = 1 ∧
      Financial.Installation.Cursor.pending input (Financial.Installation.Runtime.cursorAt input 0 19) = [] := by
  decide +kernel

theorem origin : Capitalism.Universal.Abolition.Accounting.Root.Source.OriginAt input native visit productiveClaim where
  law := rfl
  before := by
    change mechanism.code.initial = ProgrammeSource.rawCurrent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [consumed.1]
    rfl
  word := by
    change originalWord = ProgrammeSource.rawEvent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [consumed.1]
    rfl
  history := by
    change past = (List.range (Financial.Installation.Cursor.lastExecutedIndex input (original.cursor input))).map
      (fun index => ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current)
    rw [cursor_eq, consumed.1]
    rfl
  accounted := by
    change Financial.Installation.Cursor.pending input (original.cursor input) = []
    rw [cursor_eq]
    exact consumed.2

def seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response) :=
  ⟨input, 0, 19, productiveClaim, origin, []⟩

open Joint

theorem gross_quantity : (Entitlement.Source.demands (window seed)).map Entitlement.Source.Demand.quantity = [100] := by
  unfold Entitlement.Source.demands Entitlement.Source.Window.legs
  unfold Entitlement.Source.Window.before Entitlement.Source.Window.word Entitlement.Source.Window.visit
    Entitlement.Source.Window.cursor Entitlement.Source.Window.frame window seed
  simp only [Financial.Installation.Cursor.lastExecutedVisit]
  decide +kernel

def grossClaim : Entitlement.Source.Claim (window seed) :=
  (Entitlement.Source.assess (window seed)).get (by
    have nonempty : Entitlement.Source.demands (window seed) ≠ [] := by
      intro empty
      have amount := gross_quantity
      rw [empty] at amount
      cases amount
    simp [Entitlement.Source.assess, dif_pos (original_cause_is_accounted seed), dif_pos nonempty, Option.isSome_some])

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
