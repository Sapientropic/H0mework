import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Translation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)

def sourceSupport := Runtime.support seed claim visit.current

def normalizedSupport := forwardSupport seed claim (sourceSupport seed claim visit)

omit [DecidableEq Technology] in
theorem fibres : ∀ support key, Subsingleton ((NewN seed claim).OpenAt support key) :=
  Epoch.Finance.Future.Structure.extended_subsingleton (Responsibility.Family.activationLaw seed.claim)
    (fun support key => Epoch.Finance.Future.Structure.extended_subsingleton (Gross.law seed claim)
      (Background.family seed).open_fibres (unfocusedSupport seed claim support) key)

def flow : Abolition.Accounting.Root.Compiler.Flow (NewN seed claim) where
  Current := Unit
  initial := ()
  support := fun _ => normalizedSupport seed claim visit
  next := id
  writes := fun _ => true
  evolution := fun _ => LedgerWriteEvolutionAt.identity _
  finite := fun _ => @Finite.of_surjective _ _ (Runtime.entries_finite seed claim visit.current)
    (rows seed claim (sourceSupport seed claim visit)).forward
    (fun row => ⟨(rows seed claim (sourceSupport seed claim visit)).backward row,
      every_new_row_is_the_same_original_row seed claim (sourceSupport seed claim visit) row⟩)
  injective := fun _ => ⟨fun _ _ same => same,fun _ _ same => same⟩
  open_fibres := fibres seed claim

abbrev V := Abolition.Accounting.Root.Compiler.V (flow seed claim visit)
abbrev baseRoot := Abolition.Accounting.Root.Compiler.livingRoot (flow seed claim visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
