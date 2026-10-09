import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Counts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

namespace Readout
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation.Revision.Kernel
 def editing (i : Fin 17) : Bool × Bool :=
   (Sequence.anyWindow (Source.row i).word,Sequence.a8 (Source.row i).word)
 def editingConsumers : IndependentConsumerSystem (Fin 17) where
   Consumer := Unit
   Output := fun _ => Bool × Bool
   read := fun _ => editing
   positive := ⟨()⟩
 theorem editing_kernel_exact : FaceKernelExactAt editingConsumers editing := by
   intro left right
   exact ⟨fun equality _ => equality,fun equality => equality ()⟩
 def frame : IndependentReadout (Fin 17) where
   Output := Option (List String)
   read := fun i => Sequence.firstStop (Source.row i).word
 theorem actual_frame_escapes_editing : FaceKernelEscapeAt editing frame := by
   refine ⟨0,7,?_,?_⟩
   · decide +kernel
   · change Sequence.firstStop (Source.row 0).word ≠ Sequence.firstStop (Source.row 7).word
     rw [Sequence.complete_context_first_stop,Sequence.complete_context_first_stop]
     decide +kernel
 def extension := KernelExtensionDiagnosticAt.generate editingConsumers editing
   editing_kernel_exact id frame actual_frame_escapes_editing
 theorem all_consumers_preserved : type_of% extension.directConsumer := extension.directConsumer
 theorem corrected_base_and_original_frame_consumed :
    (extension.revisedFace 0).1 = (extension.revisedFace 7).1 ∧
    (extension.revisedFace 0).2 ≠ (extension.revisedFace 7).2 ∧
    (extension.revisedFace 11).1.2 = false ∧
    (extension.revisedFace 11).2 = some ((CPS1Personalized2025.Source.referenceProtein.set 334 "Y") ++ ["*"]) := by
   refine ⟨by decide +kernel,?_,by decide +kernel,?_⟩
   · change Sequence.firstStop (Source.row 0).word ≠ Sequence.firstStop (Source.row 7).word
     rw [Sequence.complete_context_first_stop,Sequence.complete_context_first_stop]
     decide +kernel
   · exact Sequence.complete_context_first_stop 11
end Readout

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
