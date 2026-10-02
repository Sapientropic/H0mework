import H0mework.Versions.R2.Physics.MotherLaws.JointSourceSource
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.SpacetimeSamples
import H0mework.Versions.R2.Physics.MotherLaws.RestrictionConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws

open StageNineEnrichedProofFreeSource StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9CU.Fields Stage9C.Revision MotherStreamLaws MotherClosedRestrictions

noncomputable section

def fieldSamples (field : StageNineHolonomicConfiguration) : Stream := fun address =>
  match Encodable.decode (α := WholeSpacetimeMaterial.Query) address with
  | none => 0
  | some query => realCoordinate field query.1 (WholeSpacetimeMaterial.rationalPoint query.2)

theorem field_recovered {first second : StageNineHolonomicConfiguration}
    (firstSmooth : first.Smooth) (secondSmooth : second.Smooth)
    (same : fieldSamples first = fieldSamples second) : first = second := by
  apply configuration_eq_of_realCoordinate_eq
  intro coordinate point
  have sampled : (realCoordinate first coordinate) ∘ WholeSpacetimeMaterial.rationalPoint =
      (realCoordinate second coordinate) ∘ WholeSpacetimeMaterial.rationalPoint := by
    funext q
    have original := congrFun same (Encodable.encode (coordinate, q))
    simpa only [fieldSamples, Encodable.encodek, Function.comp_apply] using original
  exact congrFun (WholeSpacetimeMaterial.rationalPoint_dense.dense.equalizer
    (realCoordinate_continuous firstSmooth coordinate)
    (realCoordinate_continuous secondSmooth coordinate) sampled) point

def centerSamples (center : BasePoint) : Stream := MotherStreamLaws.pad 4 center

theorem centerSamples_injective : Function.Injective centerSamples := by
  intro first second same
  apply PiLp.ext
  intro index
  have read := congrFun same index.val
  simpa only [centerSamples, MotherStreamLaws.pad, index.isLt, ↓reduceDIte] using read

abbrev Input := Σ source : SmoothUnifiedSource, GeneralSourceEvolution.State source × BasePoint

/-- Source, full field and actual writer parameter are one recoverable input. -/
def samples (input : Input) : Stream :=
  pairStream (sourceSamples input.1)
    (pairStream (fieldSamples input.2.1.current) (centerSamples input.2.2))

theorem samples_injective : Function.Injective samples := by
  rintro ⟨firstSource, firstState, firstCenter⟩ ⟨secondSource, secondState, secondCenter⟩ same
  have sources : firstSource = secondSource := sourceSamples_injective (by
    have projected := congrArg firstStream same
    simpa only [samples, first_pair] using projected)
  cases sources
  have fields : firstState.current = secondState.current := field_recovered
    firstState.smooth secondState.smooth (by
      have projected := congrArg (fun data => firstStream (lastStream data)) same
      simpa only [samples, first_pair, last_pair] using projected)
  have states : firstState = secondState := SourceFamilyEvolution.state_ext fields
  have centers : firstCenter = secondCenter := centerSamples_injective (by
    have projected := congrArg (fun data => lastStream (lastStream data)) same
    simpa only [samples, last_pair] using projected)
  cases states
  cases centers
  rfl

def encode (input : Input) : MotherStreamFormation.Carrier :=
  CurrentSampleAction.readInverse (samples input)

theorem read_encode (input : Input) : MotherStreamFormation.read (encode input) = samples input :=
  CurrentSampleAction.read_readInverse _

local instance instNonemptyInput : Nonempty Input := ⟨⟨Runtime.source, GeneralSourceEvolution.initialState Runtime.source, 0⟩⟩

def recoverSamples : Stream → Input := Function.invFun samples

theorem recover_samples (input : Input) : recoverSamples (samples input) = input :=
  Function.leftInverse_invFun samples_injective input

def recover (material : MotherStreamFormation.Carrier) : Input :=
  recoverSamples (MotherStreamFormation.read material)

theorem recover_encode (input : Input) : recover (encode input) = input := by
  rw [recover, read_encode, recover_samples]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws
