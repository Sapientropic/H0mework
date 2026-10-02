import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Cofinal

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeVisit
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

abbrev Visit (root : SourceNativeLivingRootClosure N V) :=
  SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot

/-- The two original chronological origins, with the cofinal origin
produced by its existing source emitter and full path compatibility. -/
def start (root : SourceNativeLivingRootClosure N V) : Bool → Option (Visit root)
  | false => some (.finite root.toAuthoritativeRoot.toRoot.initialVisit)
  | true => (MotherNativeAuthority.formCofinal root).map SourceNativeTemporalVisitAt.cofinal

def advance (root : SourceNativeLivingRootClosure N V) (visit : Visit root) : Option (Visit root) :=
  match next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? with
  | none => none
  | some _ => some (visit.next next_eq)

theorem advance_recovers (root : SourceNativeLivingRootClosure N V) (visit : Visit root)
    {next : V.Current}
    (next_eq : (root.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    advance root visit = some (visit.next next_eq) := by
  unfold advance
  split
  · rename_i absent
    cases next_eq.symm.trans absent
  · rename_i other produced
    have same := Option.some.inj (produced.symm.trans next_eq)
    cases same
    rfl

def generate (root : SourceNativeLivingRootClosure N V) (cofinal : Bool) : Nat → Option (Visit root)
  | 0 => start root cofinal
  | steps + 1 => (generate root cofinal steps).bind (advance root)

theorem every_finite (root : SourceNativeLivingRootClosure N V) {current : V.Current}
    (history : root.toAuthoritativeRoot.toRoot.ReachableAt current) :
    ∃ steps, generate root false steps = some ⟨current, .finite history⟩ := by
  induction history with
  | initial => exact ⟨0, rfl⟩
  | @step current next prior next_eq ih =>
    obtain ⟨steps, formed⟩ := ih
    refine ⟨steps + 1, ?_⟩
    rw [generate, formed, Option.bind_some]
    exact advance_recovers root ⟨current, .finite prior⟩ next_eq

theorem every_postCofinal (root : SourceNativeLivingRootClosure N V) {current : V.Current}
    (history : SourceNativePostCofinalReachableAt root.toAuthoritativeRoot.toLedgerRoot current) :
    ∃ steps, generate root true steps = some ⟨current, .postCofinal history⟩ := by
  induction history with
  | cofinal visit =>
    refine ⟨0, ?_⟩
    rw [generate, start, MotherNativeAuthority.formCofinal_recovers root visit]
    rfl
  | @step current next prior next_eq ih =>
    obtain ⟨steps, formed⟩ := ih
    refine ⟨steps + 1, ?_⟩
    rw [generate, formed, Option.bind_some]
    exact advance_recovers root ⟨current, .postCofinal prior⟩ next_eq

/-- Every complete original visit, including the cofinal origin and every
post-cofinal successor, is a generated value. Current labels are not used
as chronological identities. -/
theorem every_visit (root : SourceNativeLivingRootClosure N V) (visit : Visit root) :
    ∃ cofinal steps, generate root cofinal steps = some visit := by
  rcases visit with ⟨current, history⟩
  cases history with
  | finite history =>
    obtain ⟨steps, formed⟩ := every_finite root history
    exact ⟨false, steps, formed⟩
  | postCofinal history =>
    obtain ⟨steps, formed⟩ := every_postCofinal root history
    exact ⟨true, steps, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeVisit
