import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

noncomputable section

def request (person : Bool) (operation : Operation Bool Bool Unit Unit) : R :=
  ⟨person,[],false,[],operation⟩
def life (person : Bool) : R := request person (.use person [(true,1)] .necessity)
def nature (loss : ℚ) : R := request true (.use true [(false,loss)] .external)
def readFee : R := request false (.use false [(false,1)] .contribution)
def produce : R := request false (.produce false)
def loan : R := request false (.issue () false true 1)
def funding : R := request true (.transfer true false [(false,1)])
def repay : R := request false (.settle () false true 1)

def task : PublicTaskSpec Bool Bool where
  slots := [⟨false,[(true,1)],.necessity⟩]
  earliest := 0
  deadline := 100
  demand := ⟨_,List.mem_cons_self,_,List.mem_cons_self,by norm_num⟩

def code : Distributed.Code Bool Bool Bool Unit Unit where
  law := PublicFunction.physicalLaw Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.law
  initial := quoteCut
  task := task
  actions := [produce,repay]
  actionLimit := 2
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
  goods := [false,true]
  instruments := [()]
  parties_cover := by intro person; cases person <;> simp
  goods_cover := by intro good; cases good <;> simp
  instruments_cover := by intro instrument; cases instrument; simp

def mechanism : Trials.Mechanism Bool Bool Bool Unit Unit where
  code := code
  policy := fun _ _ => [produce,repay]
  terms := ⟨false,true,(),1⟩
  funding := [loan,funding]
  investment := [(false,1)]
  investmentPort := false
  probe := []
  observer := ⟨0,by decide⟩
  closing := [life false,life true]

def signal : Fin mechanism.code.signals := ⟨0,by decide⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
