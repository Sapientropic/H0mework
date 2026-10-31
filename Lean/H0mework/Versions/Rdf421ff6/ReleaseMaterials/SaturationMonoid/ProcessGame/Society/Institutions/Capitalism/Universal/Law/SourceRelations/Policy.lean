import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.PersonalUse

/-! Execution and interpretation read the same RawLaw.policy code.  No
external normalizer or transparency certificate is accepted.  An opaque
callback remains on its original item even when that request returned true. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.SourceRelations

open Source.Program Source.ProgrammeControl
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def OpaqueAt {current : RawCurrent Party Good Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} (_item : OriginalItem law current word) : Prop :=
  match law.policy with
  | .unrestricted => False
  | .settlement _ => False
  | .opaque _ => True

instance {current : RawCurrent Party Good Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} (item : OriginalItem law current word) :
    Decidable (OpaqueAt law item) := by
  unfold OpaqueAt
  cases law.policy <;> infer_instance

omit [DecidableEq Port] in
theorem opaque_true_result_is_still_unresolved
    {current : RawCurrent Party Good Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} (item : OriginalItem law current word)
    (callback : RawCurrent Party Good Technology Instrument → Request Party Good Port Technology Instrument → Bool)
    (source : law.policy = .opaque callback)
    (_observed : law.operationAllowed item.val.before item.val.request = true) : OpaqueAt law item := by
  unfold OpaqueAt
  rw [source]
  trivial

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.SourceRelations
