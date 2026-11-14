import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

abbrev V := RawGeneratedRoot.vocabulary dynamics

def rawWorld (law : MotherPhysicalLaws.Law) : SourceNativeLivingRawWorld N V where
  source := ⟨declarationSource law, (declarationSource law).emptyFaithfulTerminalHandoff
    (fun _ => ⟨fun terminal => nomatch terminal⟩)⟩
  emitted := RawGeneratedRoot.emitted dynamics

def livingRoot (law : MotherPhysicalLaws.Law) : SourceNativeLivingRootClosure N V :=
  (rawWorld law).toLivingRoot ⟨fun _ => rfl⟩

def initialVisit (law : MotherPhysicalLaws.Law) :
    SourceNativeTemporalVisitAt (livingRoot law).toAuthoritativeRoot.toLedgerRoot :=
  .finite (livingRoot law).toAuthoritativeRoot.toRoot.initialVisit

/-- These visits are the original emitted finite trajectory of this generated source. -/
def visitAt (law : MotherPhysicalLaws.Law) : ℕ →
    SourceNativeTemporalVisitAt (livingRoot law).toAuthoritativeRoot.toLedgerRoot
  | 0 => initialVisit law
  | depth + 1 => (visitAt law depth).next rfl

def entryAt (law : MotherPhysicalLaws.Law) (depth : ℕ) :
    OpenResponsibilityAt N (visitAt law depth).current :=
  RawGeneratedRoot.entry dynamics (visitAt law depth).current

def initialGenerated (law : MotherPhysicalLaws.Law) :=
  (livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (initialVisit law)

def initialEntryRow (law : MotherPhysicalLaws.Law) :
    (initialGenerated law).GeneratedEntryRowAt (entryAt law 0) :=
  ((initialGenerated law).canonicalGeneratedEntryRow? (entryAt law 0)).get (by rfl)

def authorityAt (law : MotherPhysicalLaws.Law) : (depth : ℕ) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot law) (visitAt law depth) (entryAt law depth)
  | 0 => .generatedFromInitialRow (livingRoot law) (entryAt law 0) (initialEntryRow law)
  | depth + 1 => (authorityAt law depth).next rfl

def anchorAt (law : MotherPhysicalLaws.Law) (depth : ℕ) : Anchor :=
  ⟨(visitAt law depth).current, (livingRoot law).emitted (visitAt law depth).current⟩

abbrev QueryAt (law : MotherPhysicalLaws.Law) (depth : ℕ) := Query law (anchorAt law depth)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
