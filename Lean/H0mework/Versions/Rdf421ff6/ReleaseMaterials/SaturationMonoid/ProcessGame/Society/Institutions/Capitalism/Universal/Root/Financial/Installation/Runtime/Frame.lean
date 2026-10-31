import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Compilation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Entry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

/-! A frame contains the actual source, its finite causal visit and the
original carried entry authority.  A debt birth changes its root through the
source-generated admission; ordinary motion retains that same living root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure Frame where
  native : NativeFrame input
  installed : Installed input native
  entryProtocol : EntryProtocol input native
  projectionFinite : Finite native.root.toAuthoritativeRoot.source.projectionLaw.Projection
  projectionLarge : 6 ≤ Nat.card native.root.toAuthoritativeRoot.source.projectionLaw.Projection
  visit : RootVisit native.root.toAuthoritativeRoot.toRoot
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt native.root (.finite visit)
    (entry input native visit.current)

def advanceAuthority (native : NativeFrame input) (protocol : EntryProtocol input native)
    (visit : RootVisit native.root.toAuthoritativeRoot.toRoot)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt native.root (.finite visit)
      (entry input native visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt native.root
      (.finite (visit.next (nativeNext_eq input native visit.current)))
      (entry input native (visit.next (nativeNext_eq input native visit.current)).current) := by
  change SourceNativeLivingTemporalCausalEntryAuthorityAt native.root
    ((SourceNativeTemporalVisitAt.finite visit).next (nativeNext_eq input native visit.current))
    (native.entrySupport
      (native.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (native.root.emitted (native.V.nativeTarget (native.program.emit visit.current).write))))
  rw [← protocol.entry_next visit.current]
  exact authority.next (nativeNext_eq input native visit.current)

namespace Frame
variable (frame : Frame input)

def temporal : SourceNativeTemporalVisitAt frame.native.root.toAuthoritativeRoot.toLedgerRoot := .finite frame.visit

def cursor := frame.native.cursor frame.visit.current

def presentation := Runtime.presentation input frame.native frame.installed (frame.temporal input) frame.authority

def query : (frame.presentation input).Query := PUnit.unit

theorem query_unique (candidate : (frame.presentation input).Query) : candidate = frame.query input := by
  cases candidate
  rfl

def ordinary : Frame input where
  native := frame.native
  installed := frame.installed
  entryProtocol := frame.entryProtocol
  projectionFinite := frame.projectionFinite
  projectionLarge := frame.projectionLarge
  visit := frame.visit.next (nativeNext_eq input frame.native frame.visit.current)
  authority := advanceAuthority input frame.native frame.entryProtocol frame.visit frame.authority

def born (registered : Registration input frame.native frame.visit.current) : Frame input := by
  let child := Admission.nativeFrame input frame.native registered
  let protocol := Admission.entryProtocol input frame.native registered frame.entryProtocol
  let initial := child.root.toAuthoritativeRoot.toRoot.initialVisit
  have firstAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt child.root (.finite initial)
      (entry input child initial.current) :=
    SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow child.root _
      (Admission.initialOldRow input frame.native (frame.temporal input) registered
        (entry input frame.native frame.visit.current))
  letI oldFinite : Finite frame.native.root.toAuthoritativeRoot.source.projectionLaw.Projection := frame.projectionFinite
  letI ownFinite : Finite Admission.OwnProjection := own_projection_finite
  letI : Fintype frame.native.root.toAuthoritativeRoot.source.projectionLaw.Projection := Fintype.ofFinite _
  letI : Fintype Admission.OwnProjection := Fintype.ofFinite _
  refine {
    native := child
    installed := childInstalled input frame.native registered
    entryProtocol := protocol
    projectionFinite := ?_
    projectionLarge := ?_
    visit := initial.next (nativeNext_eq input child initial.current)
    authority := advanceAuthority input child protocol initial firstAuthority }
  · change Finite (frame.native.root.toAuthoritativeRoot.source.projectionLaw.Projection ⊕ Admission.OwnProjection)
    infer_instance
  · rw [child_projection_card input frame.native registered]
    exact frame.projectionLarge.trans (Nat.le_add_right _ _)

def next : Frame input :=
  match registration? input frame.native frame.visit.current with
  | some registered => frame.born input registered
  | none => frame.ordinary input

theorem ordinary_cursor : (frame.ordinary input).cursor input = Cursor.next input (frame.cursor input) :=
  frame.native.next_exact frame.visit.current

theorem born_cursor (registered : Registration input frame.native frame.visit.current) :
    (frame.born input registered).cursor input = Cursor.next input (frame.cursor input) :=
  frame.native.next_exact frame.visit.current

theorem next_cursor : (frame.next input).cursor input = Cursor.next input (frame.cursor input) := by
  unfold next
  split
  · exact frame.born_cursor input _
  · exact frame.ordinary_cursor input

end Frame

def initialFrame (depth : Nat) : Frame input := by
  let start := Ingress.start input depth
  let positive := Ingress.start_positive input depth
  let native := AccountSource.nativeFrame input start positive
  let protocol := AccountSource.entryProtocol input start positive
  let initial := native.root.toAuthoritativeRoot.toRoot.initialVisit
  have initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt native.root (.finite initial)
      (entry input native initial.current) :=
    SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow native.root _
      (Ingress.initialRow input depth)
  exact {
    native := native
    installed := baseInstalled input start positive
    entryProtocol := protocol
    projectionFinite := base_projection_finite
    projectionLarge := base_projection_card.ge
    visit := initial.next (nativeNext_eq input native initial.current)
    authority := advanceAuthority input native protocol initial initialAuthority }

def frames (depth : Nat) : Nat → Frame input
  | 0 => initialFrame input depth
  | count + 1 => (frames depth count).next input

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
