import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Consumer.Fixture
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Compare

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact

open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

namespace Original
export Entitlement.Consumer (initial issued advanced need taking retained)
end Original

def law : RawLaw Bool Bool Bool Unit Unit := { Entitlement.Consumer.law with
  technique := fun _ _ => ⟨[],[(false,18)],[],[true]⟩ }

def before := law.next Original.initial []
def nature : Request Bool Bool Bool Unit Unit := ⟨false,[],false,[],.produce false⟩

abbrev code : Distributed.Code Bool Bool Bool Unit Unit where
  law := law
  initial := before
  task := ⟨[⟨false,[(true,1)],.necessity⟩],0,10,by decide +kernel⟩
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
  parties := [false,true]
  goods := [false,true]
  instruments := [()]
  parties_cover := by intro actor; cases actor <;> simp
  goods_cover := by intro good; cases good <;> simp
  instruments_cover := by intro instrument; cases instrument; simp

def mechanism : Trials.Mechanism Bool Bool Bool Unit Unit where
  code := code
  policy := fun _ _ => []
  terms := ⟨false,true,(),1⟩
  funding := [Original.issued,Original.advanced,Original.need,Original.taking,Original.retained]
  investment := [(true,1)]
  investmentPort := false
  probe := []
  observer := 0
  closing := []

def past : List (RawEvent Bool Bool Bool Unit Unit) := [[]]
def response : Control.HistoryResponse (Party := Bool) (Good := Bool) (Port := Bool) (Technology := Unit) (Instrument := Unit) :=
  fun _ _ _ => []
def originalWord := Control.responseWord mechanism past nature response

def input : ProgrammeSource.Input Bool Bool Bool Unit Unit where
  law := law
  initial := Original.initial
  instructions := originalWord

theorem the_productive_gap_is_the_same_sources_real_eighteen :
    Responsibility.partyLoss mechanism past nature response false false = 18 ∧
      Responsibility.controllerCohort mechanism past nature response = [true] := by decide +kernel

def productiveClaim : Responsibility.Family.Claim mechanism past nature response :=
  (Responsibility.Family.assess mechanism past nature response).get (by
    have positive : 0 < Responsibility.partyLoss mechanism past nature response false false := by
      rw [the_productive_gap_is_the_same_sources_real_eighteen.1]
      norm_num
    have member := Responsibility.Family.every_positive_original_harm_is_in_the_generated_scope
      mechanism past nature response false false positive
    have nonempty : Responsibility.Family.positiveScope mechanism past nature response ≠ [] := by
      intro empty; rw [empty] at member; exact List.not_mem_nil member
    simp [Responsibility.Family.assess,nonempty])

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
