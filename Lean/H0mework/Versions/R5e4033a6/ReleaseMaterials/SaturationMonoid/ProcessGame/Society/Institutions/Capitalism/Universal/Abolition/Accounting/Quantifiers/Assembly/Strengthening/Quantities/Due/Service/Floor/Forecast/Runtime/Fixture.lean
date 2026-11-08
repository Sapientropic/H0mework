import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Use
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Funding
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime.Consumers

open Source.Program

def numericCut : RawCurrent Bool Bool Unit Unit where
  stock := fun bearer good => if good then 1 else if bearer then 109 else 117
  claims := fun _ _ _ => 0
  technology := ()
  clock := 4
  round := 4

def numericRows : List ((Bool × Use × Bool × ℚ) × ℚ) :=
  [((false, .necessity, true, 1), 0), ((true, .necessity, true, 1), 0)]

def food (bearer : Bool) : Request Bool Bool Bool Unit Unit :=
  ⟨bearer, [], false, [], .use bearer [(true, 1)] .necessity⟩

def feePart : Request Bool Bool Bool Unit Unit :=
  ⟨false, [], false, [], .use false [(false, 1 / 2)] .external⟩

def otherUse : Request Bool Bool Bool Unit Unit :=
  ⟨false, [], false, [], .use false [(true, 1)] .external⟩

def numericWord : RawEvent Bool Bool Bool Unit Unit := [food false, food true, feePart, feePart]

theorem numericOpening : ∀ party good, 0 ≤ numericCut.stock party good := by
  intro party good
  cases party <;> cases good <;> decide +kernel

def shortage (word : RawEvent Bool Bool Bool Unit Unit) : Option (Bool × Bool × ℚ) :=
  match inspectRows numericCut numericRows word numericOpening with
  | .funded _ => none
  | .short issue =>
    some (issue.address.1, issue.address.2,
      chargeRows numericRows word issue.address - numericCut.stock issue.address.1 issue.address.2)

/-- info: (none, some (false, true, 1)) -/
#guard_msgs in
#eval (shortage numericWord, shortage [otherUse])

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime.Consumers
