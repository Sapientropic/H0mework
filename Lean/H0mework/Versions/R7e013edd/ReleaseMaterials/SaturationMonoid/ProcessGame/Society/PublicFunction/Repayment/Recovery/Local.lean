import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure Route (Party Good : Type) where
  worker : Party
  waste : Good
  feedstock : Good

variable (law : RawLaw Party Good Port Technology Instrument)
  (position : Position Party Instrument) (route : Route Party Good)
  (current : RawCurrent Party Good Technology Instrument)

def wasteTransfer : Request Party Good Port Technology Instrument :=
  ⟨position.debtor, [], law.stockPort current.technology position.debtor route.waste, [],
    .transfer position.debtor route.worker [(route.waste, 1)]⟩

def workerProduction : Request Party Good Port Technology Instrument :=
  ⟨route.worker, [], law.stockPort current.technology route.worker route.feedstock, [],
    .produce route.worker⟩

def feedstockTransfer : Request Party Good Port Technology Instrument :=
  ⟨route.worker, [], law.stockPort current.technology route.worker route.feedstock, [],
    .transfer route.worker position.debtor [(route.feedstock, 1)]⟩

def repairWord : RawEvent Party Good Port Technology Instrument :=
  [wasteTransfer law position route current, workerProduction law route current,
    feedstockTransfer law position route current]

def RepairReady : Prop :=
  (∀ item ∈ law.rawItems current (repairWord law position route current),
    law.Valid item.before item.request) ∧
  current.stock position.debtor route.feedstock <
    (law.next current (repairWord law position route current)).stock position.debtor route.feedstock

instance : Decidable (RepairReady law position route current) := by unfold RepairReady; infer_instance

inductive Outcome
  | clear (noDebt : ¬ 0 < balance position current)
  | paid (positive : 0 < balance position current) (ready : Ready law position current)
  | repair (positive : 0 < balance position current) (unready : ¬ Ready law position current)
      (ready : RepairReady law position route current)
  | blocked (positive : 0 < balance position current) (unready : ¬ Ready law position current)
      (unrepairable : ¬ RepairReady law position route current)

def produce : Outcome law position route current :=
  if positive : 0 < balance position current then
    if ready : Ready law position current then .paid positive ready
    else if repair : RepairReady law position route current then .repair positive ready repair
    else .blocked positive ready repair
  else .clear positive

def Outcome.word : Outcome law position route current → RawEvent Party Good Port Technology Instrument
  | .paid .. => candidate law position current
  | .repair .. => repairWord law position route current
  | .clear .. | .blocked .. => []

def Outcome.isRepair : Outcome law position route current → Bool
  | .repair .. => true
  | _ => false

def Outcome.isBlocked : Outcome law position route current → Bool
  | .blocked .. => true
  | _ => false

theorem repair_preserves_every_claim (ready : RepairReady law position route current) :
    (law.next current (repairWord law position route current)).claims = current.claims := by
  funext code debtor creditor
  have account := law.accepted_next_financial_balance current (repairWord law position route current)
    ready.1 code debtor creditor
  simpa [repairWord, wasteTransfer, workerProduction, feedstockTransfer, RawLaw.claimDelta] using account

theorem repair_material_balance (person : Party) (good : Good) :
    (law.next current (repairWord law position route current)).stock person good +
        law.totalDebit (law.rawItems current (repairWord law position route current)) person good =
      current.stock person good +
        law.totalCredit (law.rawItems current (repairWord law position route current)) person good :=
  law.actual_next_material_balance current (repairWord law position route current) person good

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery
