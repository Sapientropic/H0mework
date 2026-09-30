import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

abbrev EntryTotal (N : WorldRelationNetwork.{0}) := Σ support : N.Support, OpenResponsibilityAt N support

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) (R : RestructuringVocabulary.{0})

def Domain : Fin 6 → Type
  | 0 => Point source
  | 1 => Point source × EntryTotal N
  | 2 => R.Obligation
  | 3 => R.base.SourceObservation.Carrier
  | 4 => R.base.Incidence
  | 5 => R.base.Lineage

def Codomain : Fin 6 → Type
  | 0 => R.base.SourceEvent
  | 1 => R.Obligation
  | 2 => N.Responsibility
  | 3 => N.Anchor
  | 4 => N.Incidence
  | 5 => N.Lineage

abbrev Fields := ∀ index, Domain source R index → Codomain (N := N) R index

def domainAddress (coordinates : Coordinates source) (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates R) :
    ∀ index, Domain source R index ↪ B
  | 0 => coordinates.occurrence
  | 1 => productEmbedding coordinates.occurrence (sigmaEmbedding world.support world.entry)
  | 2 => vocabulary.obligation
  | 3 => vocabulary.observation
  | 4 => vocabulary.incidence
  | 5 => vocabulary.lineage

def codomainAddress (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates R) :
    ∀ index, Codomain (N := N) R index ↪ B
  | 0 => vocabulary.event
  | 1 => vocabulary.obligation
  | 2 => world.responsibility
  | 3 => world.anchor
  | 4 => world.incidence
  | 5 => world.lineage

variable {source R}

def fieldsOf (law : SourceNativeLedgerRestructuringLaw source) : Fields source law.vocabulary
  | 0 => fun point => law.sourceEventAt point.2
  | 1 => fun value => law.obligationAt value.1.2 value.2.2
  | 2 => law.responsibilityKey
  | 3 => law.anchorKey
  | 4 => law.incidenceKey
  | 5 => law.lineageKey

structure FieldLaws (fields : Fields source R) : Prop where
  responsibility : ∀ (point : Point source) (support : N.Support) (entry : OpenResponsibilityAt N support),
    fields 2 (fields 1 (point, ⟨support, entry⟩)) = entry.1
  anchor : ∀ (point : Point source) (support : N.Support) (entry : OpenResponsibilityAt N support),
    fields 3 (fields 1 (point, ⟨support, entry⟩)).sourceAnchor.identity = N.anchorAt support
  incidence : ∀ (point : Point source) (support : N.Support) (entry : OpenResponsibilityAt N support),
    fields 4 (fields 1 (point, ⟨support, entry⟩)).sourceIncidence = N.incidenceAt support
  lineage : ∀ (point : Point source) (support : N.Support) (entry : OpenResponsibilityAt N support),
    fields 5 (fields 1 (point, ⟨support, entry⟩)).lineage = N.lineageAt support
  injective : ∀ (point : Point source) (support : N.Support),
    Function.Injective (fun entry : OpenResponsibilityAt N support => fields 1 (point, ⟨support, entry⟩))

def lawOf (fields : Fields source R) (laws : FieldLaws fields) : SourceNativeLedgerRestructuringLaw source where
  vocabulary := R
  sourceEventAt := fun {current} event => fields 0 ⟨current, event⟩
  obligationAt := fun {current} event {support} entry => fields 1 (⟨current, event⟩, ⟨support, entry⟩)
  responsibilityKey := fields 2
  anchorKey := fields 3
  incidenceKey := fields 4
  lineageKey := fields 5
  responsibility_commutes := fun {current} event {support} entry => laws.responsibility ⟨current, event⟩ support entry
  anchor_commutes := fun {current} event {support} entry => laws.anchor ⟨current, event⟩ support entry
  incidence_commutes := fun {current} event {support} entry => laws.incidence ⟨current, event⟩ support entry
  lineage_commutes := fun {current} event {support} entry => laws.lineage ⟨current, event⟩ support entry
  obligationAt_injective := fun {current} event {support} => laws.injective ⟨current, event⟩ support

theorem fieldsOf_laws (law : SourceNativeLedgerRestructuringLaw source) : FieldLaws (fieldsOf law) where
  responsibility := fun point _ entry => law.responsibility_commutes point.2 entry
  anchor := fun point _ entry => law.anchor_commutes point.2 entry
  incidence := fun point _ entry => law.incidence_commutes point.2 entry
  lineage := fun point _ entry => law.lineage_commutes point.2 entry
  injective := fun point _ => law.obligationAt_injective point.2

theorem lawOf_original (law : SourceNativeLedgerRestructuringLaw source) :
    lawOf (fieldsOf law) (fieldsOf_laws law) = law := rfl

variable (coordinates : Coordinates source) (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates R)

def FieldCheck (material : M) : Prop :=
  ∀ (index : Fin 6) (input : Domain source R index), ∃! output : Codomain (N := N) R index,
    r2 material index.val (domainAddress source R coordinates world vocabulary index input)
      (codomainAddress R world vocabulary index output)

def generatedFields (material : M) (checked : FieldCheck coordinates world vocabulary material) : Fields source R :=
  fun index input => Classical.choose (checked index input)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
