import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.TransportData

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
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

theorem transportedData_next (current : (RepresentedV value).Current)
    (evolution : EvolutionAt value.2.1
      ((transportedData admission value n v w p a).current.backward current)) :
    Option.map (transportedData admission value n v w p a).current.forward evolution.nextCurrent? =
      (((transportedData admission value n v w p a).evolution current).forward evolution).nextCurrent? := by
  obtain ⟨evolution, rfl⟩ := (w.evolution (admission.currentPresentation.backward (v.current.symm current))).surjective evolution
  change Option.map (fun point => v.current (admission.currentPresentation.forward (w.current.symm point)))
      (w.evolution _ evolution).nextCurrent? =
    (evolutionAt v current ((admission.evolutionPresentation _).forward
      ((w.evolution _).symm (w.evolution _ evolution)))).nextCurrent?
  rw [Equiv.symm_apply_apply, ← w.evolution_next, Option.map_map]
  calc
    Option.map ((fun point => v.current (admission.currentPresentation.forward (w.current.symm point))) ∘ w.current)
        evolution.nextCurrent? =
      Option.map (fun point => v.current (admission.currentPresentation.forward point)) evolution.nextCurrent? := by
        congr 1
        funext point
        exact congrArg (fun point => v.current (admission.currentPresentation.forward point)) (w.current.symm_apply_apply point)
    _ = Option.map v.current (Option.map admission.currentPresentation.forward evolution.nextCurrent?) := by rw [Option.map_map]; rfl
    _ = Option.map v.current ((admission.evolutionPresentation _).forward evolution).nextCurrent? :=
      congrArg (Option.map v.current) (admission.nextCurrent_commutes _ evolution)
    _ = _ := evolutionAt_next v current _

theorem transportedData_cofinalEmit :
    Option.map (transportedData admission value n v w p a).cofinal.forward value.2.1.cofinal.emit? =
      (RepresentedV value).cofinal.emit? := by
  change Option.map (fun event => v.cofinal (admission.cofinalEventPresentation.forward (w.cofinal.symm event))) _ = _
  rw [← w.cofinal_emit, Option.map_map]
  calc
    Option.map ((fun event => v.cofinal (admission.cofinalEventPresentation.forward (w.cofinal.symm event))) ∘ w.cofinal)
        admission.ActualV.cofinal.emit? =
      Option.map (fun event => v.cofinal (admission.cofinalEventPresentation.forward event)) admission.ActualV.cofinal.emit? := by
        congr 1
        funext event
        exact congrArg (fun event => v.cofinal (admission.cofinalEventPresentation.forward event)) (w.cofinal.symm_apply_apply event)
    _ = Option.map v.cofinal (Option.map admission.cofinalEventPresentation.forward admission.ActualV.cofinal.emit?) := by rw [Option.map_map]; rfl
    _ = Option.map v.cofinal V.cofinal.emit? := congrArg (Option.map v.cofinal) admission.cofinalEmit_commutes
    _ = _ := v.cofinal_emit

theorem transportedData_cofinalPath (event : value.2.1.cofinal.Event) (index : Nat) :
    (transportedData admission value n v w p a).current.forward (value.2.1.cofinal.pathAt event index) =
      (RepresentedV value).cofinal.pathAt ((transportedData admission value n v w p a).cofinal.forward event) index := by
  obtain ⟨event, rfl⟩ := w.cofinal.surjective event
  change v.current (admission.currentPresentation.forward (w.current.symm (value.2.1.cofinal.pathAt (w.cofinal event) index))) =
    (RepresentedV value).cofinal.pathAt (v.cofinal (admission.cofinalEventPresentation.forward (w.cofinal.symm (w.cofinal event)))) index
  rw [w.cofinal_path, Equiv.symm_apply_apply, Equiv.symm_apply_apply, admission.cofinalPath_commutes, v.cofinal_path]

theorem transportedData_cofinalTarget (event : value.2.1.cofinal.Event) :
    (transportedData admission value n v w p a).current.forward (value.2.1.cofinal.target event) =
      (RepresentedV value).cofinal.target ((transportedData admission value n v w p a).cofinal.forward event) := by
  obtain ⟨event, rfl⟩ := w.cofinal.surjective event
  change v.current (admission.currentPresentation.forward (w.current.symm (value.2.1.cofinal.target (w.cofinal event)))) =
    (RepresentedV value).cofinal.target (v.cofinal (admission.cofinalEventPresentation.forward (w.cofinal.symm (w.cofinal event))))
  rw [w.cofinal_target, Equiv.symm_apply_apply, Equiv.symm_apply_apply, admission.cofinalTarget_commutes, v.cofinal_target]

end AdmissionTransport
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
