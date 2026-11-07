import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

abbrev R := Request Bool Unit Unit Unit Unit
abbrev Raw := RawCurrent Bool Unit Unit Unit

def request (person : Bool) (operation : Operation Bool Unit Unit Unit) : R :=
  ⟨person,[],(),[],operation⟩
def life (person : Bool) : R := request person (.use person [((),1)] .necessity)
def law : RawLaw Bool Unit Unit Unit Unit where
  technique := fun _ _ => ⟨[],[((),10)],[],[]⟩
  controller := fun _ _ => false
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [((),1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1
def initial : Raw := ⟨fun _ _ => 100,fun _ _ _ => 0,(),0,0⟩
def input : Root.ProgrammeSource.Input Bool Unit Unit Unit Unit where
  law := law
  initial := initial
  instructions := [life false,life true]
  localAttempts := fun _ => []

def task : PublicTaskSpec Bool Unit where
  slots := [⟨false,[((),1)],.necessity⟩]
  earliest := 0
  deadline := 100
  demand := ⟨_,List.mem_cons_self,_,List.mem_cons_self,by norm_num⟩

def nature (loss : ℚ) : R := request true (.use true [((),loss)] .external)
def readFee : R := request false (.use false [((),1)] .contribution)
def produce : R := request false (.produce false)
def loan : R := request false (.issue () false true 1)
def funding : R := request true (.transfer true false [((),1)])
def repay : R := request false (.settle () false true 1)

def code : Distributed.Code Bool Unit Unit Unit Unit where
  law := law
  initial := initial
  task := task
  actions := [produce,repay,life false,life true]
  actionLimit := 4
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun _ _ => 0
  sendCost := fun _ _ => [readFee]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.adversary (nature 2),.adversary (nature 4)]
  eventLimit := 1
  eligible := fun _ => true
  parties := [false,true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro person; cases person <;> simp
  goods_cover := by intro good; cases good; simp
  instruments_cover := by intro instrument; cases instrument; simp

def mechanism : Trials.Mechanism Bool Unit Unit Unit Unit where
  code := code
  policy := fun _ _ => [produce,repay]
  terms := ⟨false,true,(),1⟩
  funding := [loan,funding]
  investment := [((),1)]
  investmentPort := ()
  probe := []
  observer := ⟨0,by decide⟩
  closing := [life false,life true]

def sampleSignal : Fin mechanism.code.signals := ⟨0,by decide⟩

def schedule := Source.compileSchedule input initial [false,true] 2 mechanism
def quotedAmount : Option ℚ :=
  match schedule with
  | .ready source => match source.table sampleSignal with
    | .priced plan => some plan.transfer
    | .obstructed _ => none
  | _ => none

theorem both_outside_options_really_pay_living :
    (Outside.sourceOutside input initial [false,true] 2 false ()).map (fun result => result.amount) = some (-1 : ℚ) ∧
      (Outside.sourceOutside input initial [false,true] 2 true ()).map (fun result => result.amount) = some (-1 : ℚ) := by
  decide +kernel

theorem one_local_signal_covers_both_actual_risk_branches :
    mechanism.paidSignal (nature 2) = some sampleSignal ∧ mechanism.paidSignal (nature 4) = some sampleSignal := by
  decide +kernel

theorem the_source_generates_four_without_a_loading_or_probability_input : quotedAmount = some 4 := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers
