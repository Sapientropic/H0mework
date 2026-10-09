import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Genomic
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaNative

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1Deamination CPS1Deamination.ExecutionReadout
attribute [local irreducible] registeredBefore registeredOld

private theorem translation_from_registered_genome {frame : CPS1Recycling.Frame}
    (current : CPS1ReactiveField.Occurrence frame)
    (source : match genomicUpdate current 2 with
      | .rejected _ _ _ _ _ _ => False
      | .updated event => event.event.result.fired.length = 2 ∧ event.event.result.remaining = [] ∧
        event.event.dna = some (CPS1Deamination.Source.sourceProgram registeredEdits).word ∧
        event.event.peptide = some CPS1EndogenousTranslation.correctedPeptide ∧
        0 < event.event.result.stock.count .ammonia) :
    ∃ event : TranslationEvent current 2 registeredTranslationRaw,
      translateLive current 2 registeredTranslationRaw = .translated event ∧
      event.peptide = CPS1EndogenousTranslation.correctedPeptide ∧
      event.genomic.event.result.remaining = [] ∧
      0 < event.genomic.event.result.stock.count .ammonia := by
  unfold translateLive
  cases selected : genomicUpdate current 2 with
  | rejected slice available availableSource saved savedSource failure =>
    simp only [selected] at source
  | updated genomic =>
    simp only [selected] at source ⊢
    have coding : genomic.event.coding = some
        (CodingReadout.codingFromGenomic (CPS1Deamination.Source.plusReadout
          (CPS1Deamination.Source.sourceProgram registeredEdits).word)) := by
      rw [genomic.event.codingActual,source.2.2.1]
      rfl
    split
    · rename_i absent
      have impossible := coding.symm.trans absent
      cases impossible
    · rename_i codingValue found
      split
      · rename_i absent
        have impossible := source.2.2.2.1.symm.trans absent
        cases impossible
      · rename_i peptide foundPeptide
        have decoded : peptide = CPS1EndogenousTranslation.correctedPeptide :=
          Option.some.inj (foundPeptide.symm.trans source.2.2.2.1)
        split
        · exact ⟨_,rfl,decoded,source.2.1,source.2.2.2.2⟩
        · rename_i rejected
          exact False.elim (rejected (decoded ▸ (rfl : CPS1EndogenousTranslation.correctedPeptide.1 = .M)))

private theorem translation_native_paid {frame : CPS1Recycling.Frame}
    {current : CPS1ReactiveField.Occurrence frame}
    (event : TranslationEvent current 2 registeredTranslationRaw)
    (decoded : event.peptide = CPS1EndogenousTranslation.correctedPeptide)
    (remaining : event.genomic.event.result.remaining = [])
    (ammonia : 0 < event.genomic.event.result.stock.count .ammonia) :
    event.peptide = CPS1EndogenousTranslation.correctedPeptide ∧
      event.genomic.event.result.remaining = [] ∧ event.native.missing = none ∧
      (credit event.native.fired).count (.releasedPeptide event.peptide) = 1 ∧
      0 < event.native.stock.count .ammonia := by
  have inventory : event.available.Perm
      (CPS1InitiationTermination.NativeComplete.rawFuel event.peptide.2 ++ event.genomic.event.result.stock) := by
    rw [event.availableSource]
    simp only [registeredTranslationRaw,translation_raw_species]
    rw [decoded]
    exact List.perm_append_comm
  have native := CPS1InitiationTermination.NativeComplete.native_compile_complete
    event.peptide.2 event.genomic.event.result.stock event.available inventory
  have complete : event.native.missing = none := by
    rw [event.actual,event.programSource]
    exact native.2.2.1
  have birth := translation_release_is_new _ _ _ event complete
  have retained := CPS1SameEventFunction.native_ammonia_retained event.program event.available
  rw [← event.actual,event.availableSource,List.count_append] at retained
  exact ⟨decoded,remaining,complete,birth.2.1,by omega⟩

theorem registered_translation_complete :
    match translateLive registeredBefore.native.current 2 registeredTranslationRaw with
    | .genomicRejected _ => False
    | .decodingRejected _ _ _ _ => False
    | .translated event => event.peptide = CPS1EndogenousTranslation.correctedPeptide ∧
        event.genomic.event.result.remaining = [] ∧ event.native.missing = none ∧
        (credit event.native.fired).count (.releasedPeptide event.peptide) = 1 ∧
        0 < event.native.stock.count .ammonia := by
  obtain ⟨event,actual,decoded,remaining,ammonia⟩ :=
    translation_from_registered_genome registeredBefore.native.current registered_genomic_complete
  rw [actual]
  exact translation_native_paid event decoded remaining ammonia

private theorem continued_peptide_reader (edits : Target.Edits) (water additional : Nat) :
    CPS1EndogenousTranslation.continuedPeptide edits water additional =
      readPeptide (Continuation.sourceContinuation edits water additional).stock := by
  unfold CPS1EndogenousTranslation.continuedPeptide CPS1Deamination.ContinuedCoding.continuedStopChain
    CPS1Deamination.ContinuedCoding.continuedCoding readPeptide readCoding
    CPS1EndogenousTranslation.peptideFromCoding?
  simp only [Bind.bind,Option.bind_assoc]

private theorem damage_from_registered_dna {frame : CPS1Recycling.Frame}
    (current : CPS1ReactiveField.Occurrence frame)
    (dna : readDNA (liveResources current) = some registeredDNA) :
    readProteinDamage current = .prematureStop 334 1500 := by
  have generated := CPS1EndogenousTranslation.actual_peptide_generated registeredEdits registeredWater registeredAdditional
  rw [continued_peptide_reader] at generated
  have dnaSame : readDNA (liveResources current) =
      readDNA (Continuation.sourceContinuation registeredEdits registeredWater registeredAdditional).stock := by
    rw [dna,(Continuation.source_continuation_actual_readout registeredEdits registeredWater registeredAdditional).1]
    rfl
  have actualRead : actualGenePeptide current =
      readPeptide (Continuation.sourceContinuation registeredEdits registeredWater registeredAdditional).stock := by
    unfold actualGenePeptide readPeptide readCoding
    rw [dnaSame]
  have unpaid : CodingReadout.paidEighth registeredEdits (registeredWater+registeredAdditional) = false := by
    decide +kernel
  rw [unpaid] at generated
  simp only [Bool.false_eq_true,if_false] at generated
  have length := CPS1EndogenousTranslation.endogenous_lengths.2.1
  change CPS1EndogenousTranslation.uncorrectedPeptide.2.length + 1 = 334 at length
  have reference := congrArg List.length CPS1EndogenousTranslation.printed_reference_recognized.1
  simp only [List.length_map] at reference
  have referenceLength : Source.referenceProtein.length = 1500 :=
    reference.symm.trans CPS1EndogenousTranslation.endogenous_lengths.1
  unfold readProteinDamage
  rw [actualRead,generated]
  simp only [if_pos (by omega : CPS1EndogenousTranslation.uncorrectedPeptide.2.length + 1 < Source.referenceProtein.length)]
  rw [length,referenceLength]

theorem registered_before_damage : readProteinDamage registeredBefore.native.current = .prematureStop 334 1500 :=
  damage_from_registered_dna registeredBefore.native.current registered_before_dna

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
