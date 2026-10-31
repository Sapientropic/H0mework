import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Stage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def flow : Abolition.Accounting.Root.Compiler.Flow (NewN seed grossClaim) where
  Current := Stage
  initial := .pending
  support := stageSupport seed grossClaim
  next := Stage.next
  writes := fun stage => match stage with | .pending | .entered => true | .declared => false
  evolution := stageEvolution seed grossClaim
  finite := stage_entries_finite seed grossClaim
  injective := fun stage =>
    ⟨Financial.Installation.keys_imply_origin_injective _ (every_stage_keeps_the_original_keys seed grossClaim stage)
      (fibres seed grossClaim),
      Financial.Installation.keys_imply_destination_injective _ (every_stage_keeps_the_original_keys seed grossClaim stage)
      (fibres seed grossClaim)⟩
  open_fibres := fibres seed grossClaim

abbrev V := Abolition.Accounting.Root.Compiler.V (flow seed grossClaim)
abbrev baseRoot := Abolition.Accounting.Root.Compiler.livingRoot (flow seed grossClaim)

theorem the_first_actual_representation_write_enters_the_shared_current :
    ((baseRoot seed grossClaim).toAuthoritativeRoot.toRoot.evolutionAt Stage.pending).nextCurrent? = some Stage.entered :=
  Abolition.Accounting.Root.Compiler.nextEq (flow seed grossClaim) Stage.pending

theorem the_same_source_also_generates_the_old_row_side_of_gross_declaration :
    ((baseRoot seed grossClaim).toAuthoritativeRoot.toRoot.evolutionAt Stage.entered).nextCurrent? = some Stage.declared :=
  Abolition.Accounting.Root.Compiler.nextEq (flow seed grossClaim) Stage.entered

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
