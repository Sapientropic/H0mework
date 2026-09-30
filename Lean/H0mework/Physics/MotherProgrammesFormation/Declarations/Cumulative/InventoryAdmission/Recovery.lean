import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.TerminalTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

private theorem presentation_ext {A C : Type} {left right : ConstructivePresentation A C}
    (forward : left.forward = right.forward) (backward : left.backward = right.backward) : left = right := by
  cases left
  cases right
  cases forward
  cases backward
  rfl

theorem presentation_conjugate_recovers {A C X Y : Type} (left : A ≃ X) (right : C ≃ Y)
    (original : ConstructivePresentation A C) :
    presentationFromEquiv
      (left.trans ((presentationEquiv (presentationFromEquiv
        (left.symm.trans ((presentationEquiv original).trans right)))).trans right.symm)) = original := by
  apply presentation_ext
  · funext value
    change right.symm (right (original.forward (left.symm (left value)))) = original.forward value
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · funext value
    change left.symm (left (original.backward (right.symm (right value)))) = original.backward value
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

namespace AdmissionTransport

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
  {old : SourceNativeRestructuringLedgerSource N V}
  (admission : SourceNativeCompleteEventInventoryAdmission old)
  (value : SourcePair)
  (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
  (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
  (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
  (p : MotherNativeSourceOrigin.Presentation n v old.source (Represented value).source)
  (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)

theorem current_recovers :
    presentationFromEquiv (w.current.trans
      ((presentationEquiv (transportedData admission value n v w p a).current).trans v.current.symm)) =
      admission.currentPresentation :=
  presentation_conjugate_recovers w.current v.current admission.currentPresentation

theorem occurrence_recovers (current : (RepresentedV value).Current) :
    presentationFromEquiv
      ((a.event (admission.currentPresentation.backward (v.current.symm current))).trans
        ((presentationEquiv ((transportedData admission value n v w p a).occurrence current)).trans
          (eventAt p current).symm)) = admission.occurrencePresentation (v.current.symm current) :=
  presentation_conjugate_recovers (a.event _) (eventAt p current) (admission.occurrencePresentation _)

theorem evolution_recovers (current : (RepresentedV value).Current) :
    presentationFromEquiv
      ((w.evolution (admission.currentPresentation.backward (v.current.symm current))).trans
        ((presentationEquiv ((transportedData admission value n v w p a).evolution current)).trans
          (evolutionAt v current).symm)) = admission.evolutionPresentation (v.current.symm current) :=
  presentation_conjugate_recovers (w.evolution _) (evolutionAt v current) (admission.evolutionPresentation _)

theorem cofinal_recovers :
    presentationFromEquiv (w.cofinal.trans
      ((presentationEquiv (transportedData admission value n v w p a).cofinal).trans v.cofinal.symm)) =
      admission.cofinalEventPresentation :=
  presentation_conjugate_recovers w.cofinal v.cofinal admission.cofinalEventPresentation

end AdmissionTransport
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
