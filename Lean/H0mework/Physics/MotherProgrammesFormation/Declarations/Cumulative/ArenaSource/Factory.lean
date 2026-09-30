import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.ActualConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Inventory

/-! Full original structural source formation on one rank material. The
original complete inventory constructor is reused at its general N/V types. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def network (m : M) (h : MotherArenaNetwork.Check m) : WorldRelationNetwork.{0} :=
  (show {N : WorldRelationNetwork.{0} // formNetwork m = some N}
    from ⟨_, formNetwork_success m h⟩).val

theorem network_formed (m : M) (h : MotherArenaNetwork.Check m) :
    formNetwork m = some (network m h) := formNetwork_success m h

structure AccountGraphs (net base events fields : M) : Prop where
  initial : ∃! c : MotherArenaVocabulary.Current base, bit fields 4 c.val
  support : ∀ (c : MotherArenaVocabulary.Current base) (event : MotherArenaActual.EventAt base events c),
    ∃! s : Support net, r3 fields 0 c.val event.val s.val
  anchor : ∀ a : MotherArenaVocabulary.Anchor base, ∃! n : Anchor net, r2 fields 1 a.val n.val
  incidence : ∀ a : MotherArenaVocabulary.Incidence base, ∃! n : Incidence net, r2 fields 2 a.val n.val
  lineage : ∀ a : MotherArenaVocabulary.Lineage base, ∃! n : Lineage net, r2 fields 3 a.val n.val

def Compatible (net base events fields : M)
    (hn : MotherArenaNetwork.Check net) (hv : MotherArenaVocabulary.Check base)
    (graphs : AccountGraphs net base events fields) : Prop :=
  (∀ (c : (MotherArenaActual.V base hv).Current) (event : MotherArenaActual.EventAt base events c),
    Classical.choose (graphs.anchor ((MotherArenaActual.V base hv).anchorAt c)) =
      (network net hn).anchorAt (Classical.choose (graphs.support c event))) ∧
  (∀ (c : (MotherArenaActual.V base hv).Current) (event : MotherArenaActual.EventAt base events c),
    Classical.choose (graphs.incidence ((MotherArenaActual.V base hv).incidenceAt c)) =
      (network net hn).incidenceAt (Classical.choose (graphs.support c event))) ∧
  (∀ (c : (MotherArenaActual.V base hv).Current) (event : MotherArenaActual.EventAt base events c),
    Classical.choose (graphs.lineage ((MotherArenaActual.V base hv).lineageAt c)) =
      (network net hn).lineageAt (Classical.choose (graphs.support c event)))

def rootSource (net base events fields : M)
    (hn : MotherArenaNetwork.Check net) (hv : MotherArenaVocabulary.Check base)
    (ha : MotherArenaActual.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    Source (network net hn) (MotherArenaActual.V base hv) where
  initial := Classical.choose graphs.initial
  actual := MotherArenaActual.actual base events hv ha
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
  if hn : MotherArenaNetwork.Check net then
    if hv : MotherArenaVocabulary.Check base then
      if ha : MotherArenaActual.Check base events hv then
        if graphs : AccountGraphs net base events fields then
          if compatible : Compatible net base events fields hn hv graphs then
            some ⟨network net hn, MotherArenaActual.V base hv,
              MotherNativeSourceOrigin.native (rootSource net base events fields hn hv ha graphs compatible)⟩
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
  let first := (MotherArenaHigher.split rank) m
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formComponents first.1 second.1 third.1 third.2

theorem formed (net base events fields : M)
    (hn : MotherArenaNetwork.Check net) (hv : MotherArenaVocabulary.Check base)
    (ha : MotherArenaActual.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    formSource ((MotherArenaHigher.pack rank) (net, (MotherArenaHigher.pack rank)
      (base, (MotherArenaHigher.pack rank) (events, fields)))) =
      some ⟨network net hn, MotherArenaActual.V base hv,
        MotherNativeSourceOrigin.native (rootSource net base events fields hn hv ha graphs compatible)⟩ := by
  simp only [formSource, (MotherArenaHigher.split_pack rank)]
  simp only [formComponents, dif_pos hn, dif_pos hv, dif_pos ha, dif_pos graphs, dif_pos compatible]

theorem initial_selected (net base events fields : M)
    (hn : MotherArenaNetwork.Check net) (hv : MotherArenaVocabulary.Check base)
    (ha : MotherArenaActual.Check base events hv) (graphs : AccountGraphs net base events fields)
    (compatible : Compatible net base events fields hn hv graphs) :
    bit fields 4 (MotherNativeSourceOrigin.native (rootSource net base events fields hn hv ha graphs compatible)).initial.val :=
  (Classical.choose_spec graphs.initial).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
