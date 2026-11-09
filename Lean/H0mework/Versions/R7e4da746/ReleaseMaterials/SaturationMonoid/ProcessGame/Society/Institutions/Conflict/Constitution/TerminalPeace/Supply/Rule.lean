import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Cut

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers.Evolving (R W compact life)

noncomputable section

/-- A local batch turns over the original productive material and produces
one meal. The retained material is debited before it is returned. -/
def localTechnique (technology : Unit) (person : Bool) : Technique Bool Bool :=
  let old := compact.law.technique technology person
  { old with inputs := old.outputs, outputs := old.outputs ++ [(true, 1)], requiredPorts := [] }

def revisedLaw : RawLaw Bool Bool Bool Unit Unit :=
  { compact.law with
    technique := localTechnique
    policy := .opaque fun current request =>
      match request.operation with
      | .produce operator => decide (request.signer = operator)
      | _ => compact.law.operationAllowed current request }

/-- This law parameter is for interpreting a retained actual current.
Its registered initial data and original instruction inventory are inherited. -/
def revisedInput : ProgrammeSource.Input Bool Bool Bool Unit Unit :=
  { compact with law := revisedLaw }

abbrev physical := Physical.Public.interpreter revisedInput

def grow (person : Bool) : R := ⟨person, [], false, [], .produce person⟩

def personalWord (person : Bool) : W := [grow person, life person]

def renewalWord : W := personalWord false ++ personalWord true

def Stocked (raw : Original.Raw) : Prop :=
  ∀ person : Bool, 18 ≤ raw.stock person false ∧ 0 ≤ raw.stock person true

theorem the_revised_recipe_debits_original_carrier_and_returns_it_with_food (person : Bool) :
    revisedLaw.technique () person = ⟨[(false, 18)], [(false, 18), (true, 1)], [], []⟩ :=
  rfl

theorem the_revised_input_keeps_its_original_registered_data :
    revisedInput.initial = compact.initial ∧ revisedInput.instructions = compact.instructions :=
  ⟨rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply
