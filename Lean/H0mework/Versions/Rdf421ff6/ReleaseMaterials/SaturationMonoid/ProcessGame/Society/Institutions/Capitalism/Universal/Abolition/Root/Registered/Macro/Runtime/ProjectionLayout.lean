import Mathlib.Data.Finite.Sum
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Inventory

/-! A readout of the existing source factories' projection types. The base
and admission counts reflect real faces; no label is added to a root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

def sourceProjection (accounting : Bool) : Nat → Type
  | 0 => if accounting then Accounting.Projection else Reentry.Projection
  | births + 1 => SourceNativeProjectionCoface (sourceProjection accounting births) Raw.Projection ⊕ Admission.OwnProjection

def completeProjection (accounting : Bool) (births : Nat) :=
  SourceNativeProjectionCoface (sourceProjection accounting births) Raw.Projection

theorem source_projection_finite (accounting : Bool) (births : Nat) : Finite (sourceProjection accounting births) := by
  induction births with
  | zero => cases accounting <;> first | exact accounting_projection_finite | exact reentry_projection_finite
  | succ births prior =>
      let parentFinite : Finite (sourceProjection accounting births) := prior
      let raw : Finite Raw.Projection := raw_projection_finite
      let own : Finite Admission.OwnProjection := admission_projection_finite
      let inherited : Finite (SourceNativeProjectionCoface (sourceProjection accounting births) Raw.Projection) :=
        Finite.of_equiv (sourceProjection accounting births ⊕ Raw.Projection) (cofaceEquiv _ _).symm
      exact inferInstanceAs (Finite (_ ⊕ Admission.OwnProjection))

theorem source_projection_card (accounting : Bool) (births : Nat) :
    Nat.card (sourceProjection accounting births) = (if accounting then 6 else 5) + 12 * births := by
  induction births with
  | zero => cases accounting <;> first | exact accounting_projection_card | exact reentry_projection_card
  | succ births prior =>
      let parentFinite : Finite (sourceProjection accounting births) := source_projection_finite accounting births
      let raw : Finite Raw.Projection := raw_projection_finite
      let own : Finite Admission.OwnProjection := admission_projection_finite
      let inherited : Finite (SourceNativeProjectionCoface (sourceProjection accounting births) Raw.Projection) :=
        Finite.of_equiv (sourceProjection accounting births ⊕ Raw.Projection) (cofaceEquiv _ _).symm
      change Nat.card (SourceNativeProjectionCoface (sourceProjection accounting births) Raw.Projection ⊕ Admission.OwnProjection) = _
      rw [Nat.card_sum, Nat.card_congr (cofaceEquiv _ _), Nat.card_sum, raw_projection_card, admission_projection_card, prior]
      omega

theorem complete_projection_card (accounting : Bool) (births : Nat) :
    Nat.card (completeProjection accounting births) = (if accounting then 15 else 14) + 12 * births := by
  let parentFinite : Finite (sourceProjection accounting births) := source_projection_finite accounting births
  let raw : Finite Raw.Projection := raw_projection_finite
  unfold completeProjection
  rw [Nat.card_congr (cofaceEquiv _ _), Nat.card_sum, source_projection_card, raw_projection_card]
  cases accounting <;> simp <;> omega

structure ProjectionLayout (Projection : Type) where
  accounting : Bool
  births : Nat
  source_eq : Projection = sourceProjection accounting births

namespace ProjectionLayout
variable {P Q : Type} (layout : ProjectionLayout P)

include layout in
theorem finite : Finite P :=
  Eq.mp (congrArg Finite layout.source_eq).symm (source_projection_finite _ _)

theorem card : Nat.card (SourceNativeProjectionCoface P Raw.Projection) =
    (if layout.accounting then 15 else 14) + 12 * layout.births :=
  (congrArg (fun projection => Nat.card (SourceNativeProjectionCoface projection Raw.Projection)) layout.source_eq).trans
    (complete_projection_card _ _)

theorem same_shape_of_card (other : ProjectionLayout Q)
    (same : Nat.card (SourceNativeProjectionCoface P Raw.Projection) =
      Nat.card (SourceNativeProjectionCoface Q Raw.Projection)) :
    layout.accounting = other.accounting ∧ layout.births = other.births := by
  rw [layout.card, other.card] at same
  cases first : layout.accounting <;> cases second : other.accounting <;>
    simp only [first, second, Bool.false_eq_true, ↓reduceIte] at same <;> simp_all <;> omega

include layout in
theorem source_eq_of_card (other : ProjectionLayout Q)
    (same : Nat.card (SourceNativeProjectionCoface P Raw.Projection) =
      Nat.card (SourceNativeProjectionCoface Q Raw.Projection)) : P = Q := by
  obtain ⟨base, births⟩ := layout.same_shape_of_card other same
  exact layout.source_eq.trans ((congrArg₂ sourceProjection base births).trans other.source_eq.symm)

end ProjectionLayout

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace Frame
variable (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

abbrev Layout := ProjectionLayout frame.package.source.root.toAuthoritativeRoot.source.projectionLaw.Projection

def layoutOrdinary (layout : frame.Layout) : frame.ordinary.Layout := layout

def layoutBorn (layout : frame.Layout)
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    (frame.born registered).Layout where
  accounting := layout.accounting
  births := layout.births + 1
  source_eq := congrArg (fun projection => SourceNativeProjectionCoface projection Raw.Projection ⊕ Admission.OwnProjection) layout.source_eq

def layoutReenter (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (frame.reenter germ).Layout := ⟨false, 0, rfl⟩

def layoutNext (layout : frame.Layout) : frame.next.Layout := by
  unfold Frame.next Frame.nextAt
  split
  · unfold Frame.internalNext
    split
    · exact frame.layoutBorn layout _
    · exact frame.layoutOrdinary layout
  · exact frame.layoutReenter _

end Frame

variable (input depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (reader : Raw.Reader input depth count)
  (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none)

def framesLayout : (tick : Nat) →
    (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).Layout
  | 0 => ⟨true, 0, rfl⟩
  | tick + 1 => (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).layoutNext (framesLayout tick)

theorem frames_projection_mod (tick : Nat) :
    erasedProjectionCard (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).presentation.erase % 4 = 2 ∨
      erasedProjectionCard (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).presentation.erase % 4 = 3 := by
  have exactCard := (framesLayout (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).card
  change erasedProjectionCard (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).presentation.erase = _ at exactCard
  split_ifs at exactCard <;> omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.framesLayout
