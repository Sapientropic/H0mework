import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaSource.Account
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Presentation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev Presentation {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    (n : MotherNetworkOrigin.Presentation N G) (v : MotherArenaVocabulary.Presentation V W)
    (original : SourceNativeSource N V) (generated : SourceNativeSource G W) :=
  MotherNativeSourceOrigin.Presentation n v original generated

def accountPresentation {net base events fields : M}
    {hn : MotherArenaNetwork.Check net} {hv : MotherArenaVocabulary.Check base}
    {ha : MotherArenaActual.Check base events hv}
    {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (n : MotherNetworkOrigin.Presentation N (network net hn))
    (v : MotherArenaVocabulary.Presentation V (MotherArenaActual.V base hv))
    (original : SourceNativeSource N V)
    (a : MotherArenaActual.Presentation v original.toRootSource.actual (MotherArenaActual.actual base events hv ha))
    (hm : (MotherArenaHigher.read rank) fields = AccountEncoding.reader n v original.toRootSource a) :
    Presentation n v original
      (MotherNativeSourceOrigin.native (rootSource net base events fields hn hv ha
        (AccountEncoding.graphs n v original.toRootSource a hm)
        (AccountEncoding.compatible n v original.toRootSource a hm))) := by
  let root := rootSource net base events fields hn hv ha
    (AccountEncoding.graphs n v original.toRootSource a hm)
    (AccountEncoding.compatible n v original.toRootSource a hm)
  change Presentation n v original (MotherNativeSourceOrigin.native root)
  refine {
    initial_eq := AccountEncoding.initial_value n v original.toRootSource a hm
    event := fun c => (a.event c).trans (MotherNativeSourceOrigin.eventEquiv root (v.current c))
    compile_eq := ?_
    support_eq := ?_
    anchor_eq := AccountEncoding.anchor_value n v original.toRootSource a hm
    incidence_eq := AccountEncoding.incidence_value n v original.toRootSource a hm
    lineage_eq := AccountEncoding.lineage_value n v original.toRootSource a hm }
  · intro c event
    exact (MotherNativeSourceOrigin.compile_original root (a.event c event)).trans (a.compile_commutes c event)
  · intro c event
    exact (MotherNativeSourceOrigin.support_original root (a.event c event)).trans
      (AccountEncoding.support_value n v original.toRootSource a hm c event)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
