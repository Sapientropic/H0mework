import H0mework.Physics.MotherProgrammesFormation.Declarations.Conductor.Evaluator
import H0mework.Physics.MotherLaws.PointwiseRestriction

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTreeFunctions

open MotherStreamLaws MotherClosedRestrictions MotherConductorOperands
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History

noncomputable section

abbrev Input := ℕ × ConductorHistoryGenerator × SchwartzMap ℝ ℂ × ℝ

def roleFlag : ConductorHistoryRole → Bool
  | .prefix => false
  | .increment => true

/-- The node address and full evaluation input remain separate from the value being computed. -/
def inputSamples (input : Input) : Stream :=
  samples (fun _ => (input.1 : ℝ)) input.2.2.1 input.2.2.2 input.2.1.1
    (roleFlag input.2.1.2)

def nodeRead (raw : Stream) : ℕ := Nat.floor (coefficientsRead raw 0)

def generatorRead (raw : Stream) : ConductorHistoryGenerator :=
  (Nat.floor (raw 0), if raw 1 = 0 then .prefix else .increment)

theorem input_recovered (input : Input) :
    nodeRead (inputSamples input) = input.1 ∧
      generatorRead (inputSamples input) = input.2.1 ∧
      functionRead (inputSamples input) = input.2.2.1 ∧
      inputSamples input 2 = input.2.2.2 := by
  have recovered := operands_recovered (fun _ => (input.1 : ℝ)) input.2.2.1 input.2.2.2
    input.2.1.1 (roleFlag input.2.1.2)
  rw [read_encode] at recovered
  change coefficientsRead (inputSamples input) = _ ∧ _ at recovered
  refine ⟨?_, ?_, recovered.2.1, recovered.2.2.1⟩
  · rw [nodeRead, recovered.1, Nat.floor_natCast]
  · rcases input with ⟨node, ⟨cutoff, role⟩, test, scale⟩
    cases role <;> simp [generatorRead, inputSamples, samples, roleFlag]

theorem inputSamples_injective : Function.Injective inputSamples := by
  intro first last same
  have a := input_recovered first
  have b := input_recovered last
  have node := a.1.symm.trans ((congrArg nodeRead same).trans b.1)
  have generator := a.2.1.symm.trans ((congrArg generatorRead same).trans b.2.1)
  have testFunction := a.2.2.1.symm.trans ((congrArg functionRead same).trans b.2.2.1)
  have test : first.2.2.1 = last.2.2.1 := DFunLike.coe_injective testFunction
  have scale := a.2.2.2.symm.trans ((congrArg (fun raw : Stream => raw 2) same).trans b.2.2.2)
  exact Prod.ext node (Prod.ext generator (Prod.ext test scale))

def complexSamples (value : ℂ) : Stream :=
  pairStream (fun _ => value.re) (fun _ => value.im)

def complexRead (raw : Stream) : ℂ := ⟨firstStream raw 0, lastStream raw 0⟩

theorem complex_recovered (value : ℂ) : complexRead (complexSamples value) = value := by
  simp only [complexRead, complexSamples, first_pair, last_pair]

def evaluated (law : MotherPointwiseLaws.Law) (input : Input) : Stream :=
  MotherPointwiseLaws.eval law (inputSamples input)

def evaluate (law : MotherPointwiseLaws.Law) (node : ℕ) :
    ConductorHistoryGenerator → ConductorHistoryCarrier :=
  fun generator test scale => complexRead (lastStream (evaluated law ⟨node, generator, test, scale⟩))

/-- One completed law forms every node's complete function and retains the full input key. -/
theorem every_family_keyed
    (target : ℕ → ConductorHistoryGenerator → ConductorHistoryCarrier) :
    ∃ law : MotherPointwiseLaws.Law, evaluate law = target ∧
      ∀ input : Input, firstStream (evaluated law input) = inputSamples input := by
  obtain ⟨law, formed⟩ := MotherPointwiseLaws.every_restriction inputSamples inputSamples_injective
    (fun input => pairStream (inputSamples input)
      (complexSamples (target input.1 input.2.1 input.2.2.1 input.2.2.2)))
  refine ⟨law, ?_, ?_⟩
  · funext node generator test scale
    dsimp only [evaluate, evaluated]
    rw [formed, last_pair, complex_recovered]
  · intro input
    dsimp only [evaluated]
    rw [formed, first_pair]

theorem every_family
    (target : ℕ → ConductorHistoryGenerator → ConductorHistoryCarrier) :
    ∃ law : MotherPointwiseLaws.Law, evaluate law = target := by
  obtain ⟨law, formed, _⟩ := every_family_keyed target
  exact ⟨law, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTreeFunctions
