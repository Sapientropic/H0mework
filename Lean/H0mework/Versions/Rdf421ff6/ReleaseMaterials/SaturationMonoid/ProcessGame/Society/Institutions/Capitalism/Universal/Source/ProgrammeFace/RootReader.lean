import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Compilers

/-! A concrete original-source reader binds the raw execution to the literal
root successor.  A constant payload on a self-loop root cannot supply this
reader, because every raw programme tick advances its original round. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  (source : SourceNativeLedgerSource N V)
  (law : RawLaw Party Good Port Technology Instrument)

structure OriginalProgrammeReader : Type (u + 1) where
  current : V.Current → RawCurrent Party Good Technology Instrument
  event : {current : V.Current} → NativeEventAt source current →
    RawEvent Party Good Port Technology Instrument
  next_exact : {rootCurrent : V.Current} → (occurrence : ContinuingEventAt source rootCurrent) →
    current (actualTarget occurrence) = law.next (current rootCurrent) (event occurrence.val)

namespace OriginalProgrammeReader

variable {source law} (reader : OriginalProgrammeReader source law)

def raw (occurrence : OriginalOccurrence source) : Origin Party Good Port Technology Instrument :=
  ⟨reader.current occurrence.1, reader.event occurrence.2⟩

omit [DecidableEq Port] in
theorem raw_next_is_root_next {current : V.Current}
    (event : ContinuingEventAt source current) :
    reader.current (actualTarget event) = law.next (reader.current current) (reader.event event.val) :=
  reader.next_exact event

omit [DecidableEq Port] in
include reader in
theorem actual_root_target_cannot_be_identity {current : V.Current}
    (event : ContinuingEventAt source current) : actualTarget event ≠ current := by
  intro same
  have computed := reader.next_exact event
  rw [same] at computed
  exact law.two_nonidentical_currents (reader.current current) (reader.event event.val) computed.symm

end OriginalProgrammeReader

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace
