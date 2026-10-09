import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Assay
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Clinical
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel.AdjoinedConsumerKernelRevision

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel

def windowConsumers : IndependentConsumerSystem Target.Edits where
  Consumer := Unit
  Output := fun _ => Bool
  read := fun _ => Target.anyFirstWindowEdit
  positive := ⟨()⟩
theorem window_kernel_exact : FaceKernelExactAt windowConsumers Target.anyFirstWindowEdit := by
  intro left right
  exact ⟨fun eq _ => eq,fun eq => eq ()⟩
def frameReadout : IndependentReadout Target.Edits where
  Output := Option (List String)
  read := Target.stopChain
theorem frame_escapes_window_readout : FaceKernelEscapeAt Target.anyFirstWindowEdit frameReadout :=
  ⟨⟨true,false,false⟩,⟨false,true,false⟩,Target.editing_readout_does_not_determine_rescue⟩
def extension := KernelExtensionDiagnosticAt.generate windowConsumers Target.anyFirstWindowEdit
  window_kernel_exact id frameReadout frame_escapes_window_readout
theorem every_consumer_factors : type_of% extension.directConsumer := extension.directConsumer

theorem original_guide_recognizes_assay_insert :
    (Assay.row 0).site.take 20 = (DNM1Splicing2026.Sequence.render Molecules.spacer).toList ∧
    (Assay.row 0).site.drop 20 = ['A','G','C'] ∧
    (Assay.row 0).columns[0]! = "lentiviral insert" := by decide +kernel

theorem complete_program_and_response_consumed :
    type_of% Molecules.complete_editor_translation ∧
    Target.genomic ⟨false,true,false⟩ = Source.genomic ∧
    Target.stopChain ⟨false,true,false⟩ = some (Source.referenceProtein ++ ["*"]) ∧
    Assay.mean? (Assay.treated 0) = some (18361/300) ∧
    Clinical.second.patient = Clinical.first.patient ∧ Clinical.second.day = 230 ∧
    Clinical.finalMedication / Clinical.firstAttempt[2]! = 50/101 :=
  ⟨Molecules.complete_editor_translation,Target.intended_source_correction.2.1,
    Target.complete_first_stop_response false true false,Assay.original_insert_response.2.1,
    Clinical.original_same_patient_actual_redose.2.1,
    Clinical.original_same_patient_actual_redose.2.2.2.1,
    Clinical.original_taper_rollback_and_later_change.2.2.2.2.2⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Consumer
