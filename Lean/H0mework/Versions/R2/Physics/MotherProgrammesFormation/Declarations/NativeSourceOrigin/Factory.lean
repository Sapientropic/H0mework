import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Inventory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

def network (m : M) (h : MotherNetworkFactory.Check m) : WorldRelationNetwork.{0} :=
  (show {N : WorldRelationNetwork.{0} // formNetwork m = some N}
    from ⟨_, formNetwork_success m h⟩).val

theorem network_formed (m : M) (h : MotherNetworkFactory.Check m) :
    formNetwork m = some (network m h) := formNetwork_success m h

structure AccountGraphs (net base events fields : M) : Prop where
  initial : ∃! c : MotherVocabularyOrigin.Current base, bit fields 4 c.val
  support : ∀ (c : MotherVocabularyOrigin.Current base) (event : MotherActualOrigin.EventAt base events c),
    ∃! s : Support net, r3 fields 0 c.val event.val s.val
  anchor : ∀ a : MotherVocabularyOrigin.Anchor base, ∃! n : Anchor net, r2 fields 1 a.val n.val
  incidence : ∀ a : MotherVocabularyOrigin.Incidence base, ∃! n : Incidence net, r2 fields 2 a.val n.val
  lineage : ∀ a : MotherVocabularyOrigin.Lineage base, ∃! n : Lineage net, r2 fields 3 a.val n.val

def Compatible (net base events fields : M)
    (hn : MotherNetworkFactory.Check net) (hv : MotherVocabularyOrigin.Check base)
    (graphs : AccountGraphs net base events fields) : Prop :=
  (∀ (c : (MotherActualOrigin.V base hv).Current) (event : MotherActualOrigin.EventAt base events c),
    Classical.choose (graphs.anchor ((MotherActualOrigin.V base hv).anchorAt c)) =
      (network net hn).anchorAt (Classical.choose (graphs.support c event))) ∧
  (∀ (c : (MotherActualOrigin.V base hv).Current) (event : MotherActualOrigin.EventAt base events c),
    Classical.choose (graphs.incidence ((MotherActualOrigin.V base hv).incidenceAt c)) =
      (network net hn).incidenceAt (Classical.choose (graphs.support c event))) ∧
  (∀ (c : (MotherActualOrigin.V base hv).Current) (event : MotherActualOrigin.EventAt base events c),
    Classical.choose (graphs.lineage ((MotherActualOrigin.V base hv).lineageAt c)) =
      (network net hn).lineageAt (Classical.choose (graphs.support c event)))

def rootSource (net base events fields : M)
    (hn : MotherNetworkFactory.Check net) (hv : MotherVocabularyOrigin.Check base)
    (ha : MotherActualOrigin.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    Source (network net hn) (MotherActualOrigin.V base hv) where
  initial := Classical.choose graphs.initial
  actual := MotherActualOrigin.actual base events hv ha
  account := {
    supportOf := fun {c} event => Classical.choose (graphs.support c event)
    anchorKey := fun a => Classical.choose (graphs.anchor a)
    incidenceKey := fun a => Classical.choose (graphs.incidence a)
    lineageKey := fun a => Classical.choose (graphs.lineage a)
    anchor_commutes := fun {c} event => compatible.1 c event
    incidence_commutes := fun {c} event => compatible.2.1 c event
    lineage_commutes := fun {c} event => compatible.2.2 c event }

def formComponents (net base events fields : M) :
    Option (Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeSource N V) :=
  if hn : MotherNetworkFactory.Check net then
    if hv : MotherVocabularyOrigin.Check base then
      if ha : MotherActualOrigin.Check base events hv then
        if graphs : AccountGraphs net base events fields then
          if compatible : Compatible net base events fields hn hv graphs then
            some ⟨network net hn, MotherActualOrigin.V base hv,
              native (rootSource net base events fields hn hv ha graphs compatible)⟩
          else none
        else none
      else none
    else none
  else none

/-- One mother material forms the original full structural source: network,
vocabulary, complete events and compilation, initial, support, all account
keys and full affected inventory. There is no externally supplied source. -/
def formSource (m : M) :
    Option (Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeSource N V) :=
  let first := MotherHigherLawValue.split m
  let second := MotherHigherLawValue.split first.2
  let third := MotherHigherLawValue.split second.2
  formComponents first.1 second.1 third.1 third.2

theorem formed (net base events fields : M)
    (hn : MotherNetworkFactory.Check net) (hv : MotherVocabularyOrigin.Check base)
    (ha : MotherActualOrigin.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    formSource (MotherHigherLawValue.pack (net, MotherHigherLawValue.pack
      (base, MotherHigherLawValue.pack (events, fields)))) =
      some ⟨network net hn, MotherActualOrigin.V base hv,
        native (rootSource net base events fields hn hv ha graphs compatible)⟩ := by
  simp only [formSource, MotherHigherLawValue.split_pack]
  simp only [formComponents, dif_pos hn, dif_pos hv, dif_pos ha, dif_pos graphs, dif_pos compatible]

theorem initial_selected (net base events fields : M)
    (hn : MotherNetworkFactory.Check net) (hv : MotherVocabularyOrigin.Check base)
    (ha : MotherActualOrigin.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    bit fields 4 (native (rootSource net base events fields hn hv ha graphs compatible)).initial.val :=
  (Classical.choose_spec graphs.initial).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
