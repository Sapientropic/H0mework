import H0mework.Physics.MotherProgrammesFormation.Declarations.Conductor.Operands
import H0mework.Arithmetic.RiemannGraph.RuntimeMuntzConductorHistoryMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.MotherFormation

open CanonicalUnitArithmeticRoot Material
open CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open ClozelGeneralizedDual ClozelGeneralizedDual.MuntzConductor
open _root_.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
open MotherConductorOperands

noncomputable section

def nativeTerm (material : MotherStreamFormation.Carrier) (index : ℕ) : ℂ :=
  let raw := MotherStreamFormation.read material
  let point := ((index + 1 : ℕ) : ℝ) * raw 2
  (coefficientsRead raw (index + 1) : ℂ) *
    (functionRead raw point + functionRead raw (-point))

def nativeEvaluation (material : MotherStreamFormation.Carrier) : ℂ :=
  let raw := MotherStreamFormation.read material
  let cutoff := Nat.floor (raw 0)
  if raw 1 = 0 then ∑ index ∈ Finset.range cutoff, nativeTerm material index
  else nativeTerm material cutoff

theorem nativeTerm_encode (coefficients : ℕ → ℝ) (test : SchwartzMap ℝ ℂ)
    (scale : ℝ) (cutoff : ℕ) (increment : Bool) (index : ℕ) :
    nativeTerm (encode coefficients test scale cutoff increment) index =
      (coefficients (index + 1) : ℂ) *
        coPoissonMuntzEvenSource test (((index + 1 : ℕ) : ℝ) * scale) := by
  have recovered := operands_recovered coefficients test scale cutoff increment
  dsimp only at recovered
  dsimp only [nativeTerm]
  rw [recovered.1, recovered.2.1, recovered.2.2.1]
  rfl

/-- Only the fixed owner's generated inverse/commutator and actual operands enter. -/
def sourceInput (test : SchwartzMap ℝ ℂ) (scale : ℝ)
    (generator : ConductorHistoryGenerator) : MotherStreamFormation.Carrier :=
  encode (generatedEulerConductorCurrent globalEulerConductorOccurrence.root.1.1)
    test scale generator.1 (match generator.2 with
      | .prefix => false
      | .increment => true)

theorem generator_original
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt observation nontrivial occurrence)
    (generator : ConductorHistoryGenerator) :
    (fun test scale => nativeEvaluation (sourceInput test scale generator)) =
      conductorHistoryGeneratorValue face generator := by
  funext test scale
  have coefficients := face.eulerConductorCurrent_eq_global.trans
    globalEulerConductorOccurrence.root.2.conductorCurrent_eq
  rcases generator with ⟨cutoff, role⟩
  cases role <;>
    simp only [sourceInput, nativeEvaluation, read_encode, samples, Nat.floor_natCast,
      Bool.false_eq_true, ↓reduceIte, one_ne_zero, nativeTerm_encode]
  · unfold conductorHistoryGeneratorValue runtimeFaceConductorDilationPrefix
      arithmeticPositiveDilationPrefix arithmeticPositiveDilationTerm
    rw [coefficients]
  · unfold conductorHistoryGeneratorValue runtimeFaceConductorDilationTerm
      arithmeticPositiveDilationTerm
    rw [coefficients]

theorem installed_evaluator
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (fun generator test scale => nativeEvaluation (sourceInput test scale generator)) =
      ((runtimeConductorFaithfulMaterialLaw observation nontrivial).evaluatorAt occurrence).root := by
  rw [runtimeConductorFaithfulMaterialLaw_evaluator_root]
  funext generator
  exact generator_original _ generator

def nativeFold : (ConductorHistoryGenerator →₀ ℤ) →ₗ[ℤ] ConductorHistoryCarrier :=
  (Finsupp.liftAddHom fun generator =>
    AddMonoidHom.flip (smulAddHom ℤ ConductorHistoryCarrier)
      (fun test scale => nativeEvaluation (sourceInput test scale generator))).toIntLinearMap

theorem fold_original
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt observation nontrivial occurrence) :
    nativeFold = conductorHistoryFreeEvaluation face := by
  have generators : (fun generator test scale =>
      nativeEvaluation (sourceInput test scale generator)) =
        conductorHistoryGeneratorValue face := by
    funext generator
    exact generator_original face generator
  exact congrArg (fun values : ConductorHistoryGenerator → ConductorHistoryCarrier =>
    (Finsupp.liftAddHom fun generator =>
      AddMonoidHom.flip (smulAddHom ℤ ConductorHistoryCarrier)
        (values generator)).toIntLinearMap) generators

end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.MotherFormation
