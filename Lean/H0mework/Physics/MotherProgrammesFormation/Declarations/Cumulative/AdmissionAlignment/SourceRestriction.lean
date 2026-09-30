import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.CompilerRestriction

/-! Original-index source restriction. The original event and inventory
types are inverse-presentation indices; all source functions and complete
inventory presentation programs are read back from the generated source. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def restrictedInitial (_p : MotherNativeSourceOrigin.Presentation n v original generated) : V.Current :=
  v.current.symm generated.initial

theorem restrictedInitial_eq : restrictedInitial p = original.initial :=
  (congrArg v.current.symm p.initial_eq).trans (v.current.symm_apply_apply original.initial)

def restrictedStructural (current : V.Current) (support : N.Support)
    (event : original.law.EventAt current support) : EvolutionAt V current :=
  (v.evolution current).symm (generated.toRootSource.actual.compile (p.event current ⟨support, event⟩))

theorem restrictedStructural_eq : restrictedStructural p =
    fun (current : V.Current) (support : N.Support) (event : original.law.EventAt current support) => original.law.compile event := by
  funext current support event
  exact (congrArg (v.evolution current).symm (p.compile_eq current ⟨support, event⟩)).trans
    ((v.evolution current).symm_apply_apply _)

def restrictedInventory (current : V.Current) (support : N.Support)
    (event : original.law.EventAt current support) :
    ConstructivePresentation (original.law.AffectedInventoryAt event) (OpenResponsibilityAt N support) :=
  presentationFromEquiv ((p.inventory ⟨support, event⟩).trans
    ((presentationEquiv (generated.law.affectedInventoryPresentation (p.event current ⟨support, event⟩).2)).trans
      ((n.ledger support).trans (Equiv.cast
        (congrArg (OpenResponsibilityAt G) (p.support_eq current ⟨support, event⟩).symm))).symm))

private theorem presentation_ext {A B : Type} {first last : ConstructivePresentation A B}
    (forward : first.forward = last.forward) (backward : first.backward = last.backward) : first = last := by
  cases first
  cases last
  cases forward
  cases backward
  rfl

theorem restrictedInventory_eq : restrictedInventory p =
    fun (current : V.Current) (support : N.Support) (event : original.law.EventAt current support) =>
      original.law.affectedInventoryPresentation event := by
  funext current support event
  let oldInventory := presentationEquiv (original.law.affectedInventoryPresentation event)
  let newInventory := presentationEquiv
    (generated.law.affectedInventoryPresentation (p.event current ⟨support, event⟩).2)
  let middle := (n.ledger support).trans
    (Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq current ⟨support, event⟩).symm))
  apply presentation_ext
  · funext value
    change middle.symm (newInventory (newInventory.symm (middle (oldInventory value)))) = _
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl
  · funext entry
    change oldInventory.symm (middle.symm (newInventory (newInventory.symm (middle entry)))) = _
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl

def restrictedAnchor (_p : MotherNativeSourceOrigin.Presentation n v original generated) : V.Anchor → N.Anchor :=
  fun value => n.anchor.symm (generated.law.anchorKey (v.anchor value))
def restrictedIncidence (_p : MotherNativeSourceOrigin.Presentation n v original generated) : V.Incidence → N.Incidence :=
  fun value => n.incidence.symm (generated.law.incidenceKey (v.incidence value))
def restrictedLineageKey (_p : MotherNativeSourceOrigin.Presentation n v original generated) : V.Lineage → N.Lineage :=
  fun value => n.lineage.symm (generated.law.lineageKey (v.lineage value))

theorem restrictedAnchor_eq : restrictedAnchor p = original.law.anchorKey := by
  funext value
  exact (congrArg n.anchor.symm (p.anchor_eq value)).trans (n.anchor.symm_apply_apply _)
theorem restrictedIncidence_eq : restrictedIncidence p = original.law.incidenceKey := by
  funext value
  exact (congrArg n.incidence.symm (p.incidence_eq value)).trans (n.incidence.symm_apply_apply _)
theorem restrictedLineageKey_eq : restrictedLineageKey p = original.law.lineageKey := by
  funext value
  exact (congrArg n.lineage.symm (p.lineage_eq value)).trans (n.lineage.symm_apply_apply _)

private def sourceFromReadbacks
    (initial : V.Current)
    (compile : ∀ current support, original.law.EventAt current support → EvolutionAt V current)
    (inventory : ∀ current support (event : original.law.EventAt current support),
      ConstructivePresentation (original.law.AffectedInventoryAt event) (OpenResponsibilityAt N support))
    (anchor : V.Anchor → N.Anchor) (anchor_eq : anchor = original.law.anchorKey)
    (incidence : V.Incidence → N.Incidence) (incidence_eq : incidence = original.law.incidenceKey)
    (lineage : V.Lineage → N.Lineage) (lineage_eq : lineage = original.law.lineageKey) :
    SourceNativeSource N V := {
  initial := initial
  law := {
    EventAt := original.law.EventAt
    compile := fun {current} {support} event => compile current support event
    AffectedInventoryAt := original.law.AffectedInventoryAt
    affectedInventoryPresentation := fun {current} {support} event => inventory current support event
    anchorKey := anchor
    incidenceKey := incidence
    lineageKey := lineage
    anchor_commutes := fun {current} {_support} event =>
      (congrFun anchor_eq (V.anchorAt current)).trans (original.law.anchor_commutes event)
    incidence_commutes := fun {current} {_support} event =>
      (congrFun incidence_eq (V.incidenceAt current)).trans (original.law.incidence_commutes event)
    lineage_commutes := fun {current} {_support} event =>
      (congrFun lineage_eq (V.lineageAt current)).trans (original.law.lineage_commutes event) }
}

def restrictSource : SourceNativeSource N V :=
  sourceFromReadbacks (restrictedInitial p) (restrictedStructural p) (restrictedInventory p)
    (restrictedAnchor p) (restrictedAnchor_eq p) (restrictedIncidence p) (restrictedIncidence_eq p)
    (restrictedLineageKey p) (restrictedLineageKey_eq p)

theorem restrictSource_eq : restrictSource p = original := by
  unfold restrictSource
  simp only [restrictedInitial_eq, restrictedStructural_eq, restrictedInventory_eq,
    restrictedAnchor_eq, restrictedIncidence_eq, restrictedLineageKey_eq]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
