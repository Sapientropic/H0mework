import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization

/-!
# Source-witness refinement of an authority observer

A coarse observer may identify two actual occurrences whose source-native
authority differs.  This module records the smallest lawful positive escape:
an occurrence-indexed witness family publishes one total Boolean tag.  The
publication law mentions witness inhabitation only; it stores neither the
occurrence nor its authority value.

If one exact authority-kernel endpoint owns a witness and the other endpoint
has an empty witness fibre, honest publication strictly separates their
refined visible images while preserving the old coarse image.  On the exact
finite two-point restriction, the publication tag then supports a faithful
occurrence reconstruction and hence an authority factorization.  These are
post-emission consumers of the refined readout, not fields of the publication
source.

This module creates no root, ledger, registry, occurrence family, authority
oracle, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Observer

universe uOccurrence uVisible uResidual uWitness

variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Residual : Type uResidual}
variable {WitnessAt : Occurrence → Type uWitness}
variable {O : AuthorityObserver Occurrence Visible Residual}

/-! ## Total source-witness publication -/

/-- A total publication readout for a source-owned witness family.  Honesty
means exactly that the public bit is true when the indexed witness fibre is
inhabited.  No occurrence or authority value is stored in the public output. -/
structure SourceWitnessPublicationAt
    (WitnessAt : Occurrence → Type uWitness) where
  publicationTag : Occurrence → Bool
  publicationTag_eq_true_iff : ∀ occurrence,
    publicationTag occurrence = true ↔ Nonempty (WitnessAt occurrence)

namespace SourceWitnessPublicationAt

variable (publication : SourceWitnessPublicationAt WitnessAt)

theorem publicationTag_eq_true
    {occurrence : Occurrence}
    (witness : Nonempty (WitnessAt occurrence)) :
    publication.publicationTag occurrence = true :=
  (publication.publicationTag_eq_true_iff occurrence).2 witness

theorem publicationTag_eq_false
    {occurrence : Occurrence}
    (empty : IsEmpty (WitnessAt occurrence)) :
    publication.publicationTag occurrence = false := by
  cases tag_eq : publication.publicationTag occurrence with
  | false => rfl
  | true =>
      rcases (publication.publicationTag_eq_true_iff occurrence).1 tag_eq with
        ⟨witness⟩
      exact (empty.false witness).elim

end SourceWitnessPublicationAt

/-! ## Refined observer -/

/-- The refined visible image adds only the witness-publication bit to the
coarse observer image. -/
structure SourceWitnessRefinedVisible (Visible : Type uVisible) where
  coarse : Visible
  witnessPublished : Bool

/-- Refinement of an existing observer by an honest source-witness
publication.  Its authority coordinate is inherited unchanged from the old
observer and never enters the publication readout. -/
def sourceWitnessRefinedObserver
    (O : AuthorityObserver Occurrence Visible Residual)
    (publication : SourceWitnessPublicationAt WitnessAt) :
    AuthorityObserver Occurrence (SourceWitnessRefinedVisible Visible) Residual where
  forget := fun occurrence =>
    ⟨O.forget occurrence, publication.publicationTag occurrence⟩
  authorityK := O.authorityK

@[simp] theorem sourceWitnessRefinedObserver_coarse
    (publication : SourceWitnessPublicationAt WitnessAt)
    (occurrence : Occurrence) :
    ((sourceWitnessRefinedObserver O publication).forget occurrence).coarse =
      O.forget occurrence :=
  rfl

@[simp] theorem sourceWitnessRefinedObserver_witnessPublished
    (publication : SourceWitnessPublicationAt WitnessAt)
    (occurrence : Occurrence) :
    SourceWitnessRefinedVisible.witnessPublished
        ((sourceWitnessRefinedObserver O publication).forget occurrence) =
      publication.publicationTag occurrence :=
  rfl

@[simp] theorem sourceWitnessRefinedObserver_authorityK
    (publication : SourceWitnessPublicationAt WitnessAt)
    (occurrence : Occurrence) :
    (sourceWitnessRefinedObserver O publication).authorityK occurrence =
      O.authorityK occurrence :=
  rfl

/-- A publication tag which does not distinguish an old kernel pair cannot
create a distinction merely by being paired with the same coarse image. -/
theorem sourceWitnessRefinedObserver_pair_eq_of_publicationTag_eq
    (publication : SourceWitnessPublicationAt WitnessAt)
    (pair : AuthorityKernelPair O)
    (publicationTag_eq :
      publication.publicationTag pair.left =
        publication.publicationTag pair.right) :
    (sourceWitnessRefinedObserver O publication).forget pair.left =
      (sourceWitnessRefinedObserver O publication).forget pair.right := by
  exact congrArg₂ SourceWitnessRefinedVisible.mk
    pair.visible_eq publicationTag_eq

/-- Negative control: if neither endpoint owns a witness, honest publication
preserves the old visible kernel even though the endpoints still carry
different authority. -/
theorem sourceWitnessRefinedObserver_pair_eq_of_bothWitnessFibresEmpty
    (publication : SourceWitnessPublicationAt WitnessAt)
    (pair : AuthorityKernelPair O)
    (leftEmpty : IsEmpty (WitnessAt pair.left))
    (rightEmpty : IsEmpty (WitnessAt pair.right)) :
    (sourceWitnessRefinedObserver O publication).forget pair.left =
      (sourceWitnessRefinedObserver O publication).forget pair.right := by
  apply sourceWitnessRefinedObserver_pair_eq_of_publicationTag_eq
    publication pair
  rw [publication.publicationTag_eq_false leftEmpty,
    publication.publicationTag_eq_false rightEmpty]

/-! ## Exact kernel-pair refinement -/

/-- The exact source facts which let publication refine one authority-kernel
pair.  Separation and reconstruction are theorem outputs, not constructor
fields. -/
structure SourceWitnessKernelRefinementAt
    (publication : SourceWitnessPublicationAt WitnessAt)
    (pair : AuthorityKernelPair O) : Prop where
  leftWitness : Nonempty (WitnessAt pair.left)
  rightWitnessEmpty : IsEmpty (WitnessAt pair.right)

/-- Source-witness producer mouth.  It accepts only the exact kernel pair and
the two indexed witness-fibre facts; no desired visible distinction,
occurrence decoder, authority decoder, or reconstruction is supplied. -/
theorem sourceWitnessKernelRefinement
    (publication : SourceWitnessPublicationAt WitnessAt)
    (pair : AuthorityKernelPair O)
    (leftWitness : Nonempty (WitnessAt pair.left))
    (rightWitnessEmpty : IsEmpty (WitnessAt pair.right)) :
    SourceWitnessKernelRefinementAt publication pair :=
  ⟨leftWitness, rightWitnessEmpty⟩

namespace SourceWitnessKernelRefinementAt

variable {publication : SourceWitnessPublicationAt WitnessAt}
variable {pair : AuthorityKernelPair O}

variable (refinement : SourceWitnessKernelRefinementAt publication pair)

@[simp] theorem left_publicationTag_eq_true
    (refinement : SourceWitnessKernelRefinementAt publication pair) :
    publication.publicationTag pair.left = true :=
  publication.publicationTag_eq_true
    (SourceWitnessKernelRefinementAt.leftWitness refinement)

@[simp] theorem right_publicationTag_eq_false
    (refinement : SourceWitnessKernelRefinementAt publication pair) :
    publication.publicationTag pair.right = false :=
  publication.publicationTag_eq_false
    (SourceWitnessKernelRefinementAt.rightWitnessEmpty refinement)

/-- Honest witness publication strictly separates the two old kernel
endpoints at the level of the new public bit. -/
theorem publicationTag_ne
    (refinement : SourceWitnessKernelRefinementAt publication pair) :
    publication.publicationTag pair.left ≠
      publication.publicationTag pair.right := by
  rw [left_publicationTag_eq_true refinement,
    right_publicationTag_eq_false refinement]
  decide

/-- The old observer still identifies the pair.  Refinement does not rewrite
or deny the original coarse readout. -/
theorem coarseVisible_eq
    (_refinement : SourceWitnessKernelRefinementAt publication pair) :
    O.forget pair.left = O.forget pair.right :=
  pair.visible_eq

/-- Strong generic escape theorem: one inhabited/empty source-witness split
makes the exact authority-kernel endpoints visibly distinct after refinement. -/
theorem refinedVisible_ne
    (refinement : SourceWitnessKernelRefinementAt publication pair) :
    (sourceWitnessRefinedObserver O publication).forget pair.left ≠
      (sourceWitnessRefinedObserver O publication).forget pair.right := by
  intro refinedEq
  exact publicationTag_ne refinement
    (congrArg SourceWitnessRefinedVisible.witnessPublished refinedEq)

/-! ## Finite two-point posterior consumer -/

/-- The exact two-point occurrence restriction is represented by a Boolean
index only in this downstream finite consumer.  `true` realizes the witnessed
left endpoint and `false` the unwitnessed right endpoint. -/
def exactOccurrence
    (_refinement : SourceWitnessKernelRefinementAt publication pair)
    (side : Bool) : Occurrence :=
  match side with
  | true => pair.left
  | false => pair.right

@[simp] theorem exactOccurrence_true :
    refinement.exactOccurrence true = pair.left :=
  rfl

@[simp] theorem exactOccurrence_false :
    refinement.exactOccurrence false = pair.right :=
  rfl

/-- The Boolean restriction does not collapse the two actual endpoints. -/
theorem exactOccurrence_injective :
    Function.Injective refinement.exactOccurrence := by
  intro leftSide rightSide occurrenceEq
  cases leftSide <;> cases rightSide
  · rfl
  · exact (pair.occurrence_ne occurrenceEq.symm).elim
  · exact (pair.occurrence_ne occurrenceEq).elim
  · rfl

/-- Pull the source authority back to the exact two-point restriction and use
only the publication tag as its visible carrier. -/
def twoPointObserver : AuthorityObserver Bool Bool Residual where
  forget := fun side =>
    publication.publicationTag (refinement.exactOccurrence side)
  authorityK := fun side => O.authorityK (refinement.exactOccurrence side)

/-- On the exact two-point restriction, honest publication is definitionally
recoverable as the side index. -/
@[simp] theorem twoPointObserver_forget (side : Bool) :
    refinement.twoPointObserver.forget side = side := by
  cases side
  · exact refinement.right_publicationTag_eq_false
  · exact refinement.left_publicationTag_eq_true

@[simp] theorem twoPointObserver_authorityK (side : Bool) :
    refinement.twoPointObserver.authorityK side =
      O.authorityK (refinement.exactOccurrence side) :=
  rfl

/-- The two-point visible tag is a readout of the full refined visible image,
so the finite consumer does not introduce a second source of visibility. -/
theorem twoPoint_forget_factorsThroughRefinedVisible (side : Bool) :
    refinement.twoPointObserver.forget side =
      ((sourceWitnessRefinedObserver O publication).forget
        (refinement.exactOccurrence side)).witnessPublished :=
  rfl

/-- Exact occurrence readout used only after restricting to the two generated
endpoints. -/
def twoPointOccurrenceReadout
    (_refinement : SourceWitnessKernelRefinementAt publication pair) :
    OccurrenceReadout Bool Bool where
  read := id

/-- The identity readout factors through the now-separating publication tag. -/
def twoPointReadoutFactorization :
    ReadoutFactorization refinement.twoPointObserver
      refinement.twoPointOccurrenceReadout where
  visibleReadout := id
  factorizes := fun side => (refinement.twoPointObserver_forget side).symm

/-- Exact occurrence completeness is proved after publication; it is not a
field of the witness source or publication law. -/
theorem twoPointActualOccurrenceCompleteReadout :
    ActualOccurrenceCompleteReadoutAt refinement.twoPointOccurrenceReadout where
  readsActualOccurrence := fun _ => rfl

/-- The total two-point publication image has a post-hoc surrogate section. -/
def twoPointSurrogateRightSection :
    SurrogateRightSection refinement.twoPointObserver where
  lift := id
  lift_forget := refinement.twoPointObserver_forget

/-- Posterior two-point reconstruction forced by the generic readout
factorization mechanism. -/
def twoPointForcedActualReconstruction :
    ForcedActualReconstruction refinement.twoPointObserver :=
  refinement.twoPointReadoutFactorization.forceActualReconstruction
    refinement.twoPointSurrogateRightSection
    refinement.twoPointActualOccurrenceCompleteReadout

/-- The fixed two-point witness-refined consumer faithfully reconstructs its
exact occurrence side and the inherited source authority. -/
def twoPointFaithfulAuthorityReconstruction :
    FaithfulAuthorityReconstruction refinement.twoPointObserver :=
  refinement.twoPointForcedActualReconstruction
    |>.toFaithfulAuthorityReconstruction

/-- Authority factorization is generated only on the exact finite
two-point restriction whose witness publication has separated every point. -/
def twoPointAuthorityFactorization :
    AuthorityFactorization refinement.twoPointObserver :=
  refinement.twoPointFaithfulAuthorityReconstruction
    |>.toAuthorityFactorization

end SourceWitnessKernelRefinementAt

end Observer
end Society
end ProcessGame
end SaturationMonoid
