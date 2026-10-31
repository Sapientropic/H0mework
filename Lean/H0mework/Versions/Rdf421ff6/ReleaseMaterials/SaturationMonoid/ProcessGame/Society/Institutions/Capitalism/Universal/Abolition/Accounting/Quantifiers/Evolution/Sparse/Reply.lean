import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Gate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

/-- The existing refusal classification and original liability, read on the
same sparse source. No new debt, registry or damage is created by this reply. -/
structure Reply : Type where
  originalWord : RawEvent Party Good Port Technology Instrument
  executableWord : RawEvent Party Good Port Technology Instrument
  remainder : RawEvent Party Good Port Technology Instrument
  original_eq : originalWord = Input.readWord claim current word
  executable_eq : executableWord = Gate.executableWord claim current word
  whole_word : originalWord = executableWord ++ remainder
  classification : Priority.Refusal.Classification claim (Current.state claim (Input.native claim current word))
    (Current.readLaw claim (Input.native claim current word)) (Current.readMembers claim (Input.native claim current word))
    (Input.readWord claim current word) (Gate.readRenewal claim current word)
  liability : Priority.Refusal.LiabilityAt claim (Current.state claim current) current.actualLaw current.members
    (Gate.executableWord claim current word)

def reply : Reply claim current word where
  originalWord := Input.readWord claim current word
  executableWord := Gate.executableWord claim current word
  remainder := (Gate.readEvaluation claim current word).remainder
  original_eq := rfl
  executable_eq := rfl
  whole_word := (Gate.readEvaluation claim current word).original
  classification := Priority.Refusal.classify claim _ _ _ _ (Gate.readRenewal claim current word)
  liability := Priority.Refusal.carryLiability claim _ _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
