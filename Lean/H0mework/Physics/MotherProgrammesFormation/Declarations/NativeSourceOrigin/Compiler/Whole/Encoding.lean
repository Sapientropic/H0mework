import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Pages
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Section

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler.WholeEncoding
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)
    (ledgerCoordinates : LedgerCoordinates N)

def page {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (branch : EvolutionAt V current) (target : TargetFor source branch) (data : LedgerFor source event branch target) :
    Nat → B → B → Prop := by
  cases branch
  · exact writePage ledgerCoordinates data
  · exact writePage ledgerCoordinates data
  · exact writePage ledgerCoordinates data
  · exact writePage ledgerCoordinates data
  · exact terminalPage ledgerCoordinates data

theorem checkOfPage {material : M} {context : B} {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) (branch : EvolutionAt V current)
    (target : TargetFor source branch) (data : LedgerFor source event branch target)
    (graph : ∀ tag input output, r3 material tag context input output ↔
      page source ledgerCoordinates event branch target data tag input output) :
    WholeCheck ledgerCoordinates source material context event branch target := by
  cases branch
  · exact writeCheckOfPage ledgerCoordinates data graph
  · exact writeCheckOfPage ledgerCoordinates data graph
  · exact writeCheckOfPage ledgerCoordinates data graph
  · exact writeCheckOfPage ledgerCoordinates data graph
  · exact terminalCheckOfPage ledgerCoordinates data graph

theorem whole_eq_of_page {material : M} {context : B} {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) (branch : EvolutionAt V current)
    (target : TargetFor source branch) (data : LedgerFor source event branch target)
    (graph : ∀ tag input output, r3 material tag context input output ↔
      page source ledgerCoordinates event branch target data tag input output) :
    whole ledgerCoordinates source material context event branch target
      (checkOfPage source ledgerCoordinates event branch target data graph) = data := by
  cases branch
  · exact write_eq_of_page ledgerCoordinates data graph
  · exact write_eq_of_page ledgerCoordinates data graph
  · exact write_eq_of_page ledgerCoordinates data graph
  · exact write_eq_of_page ledgerCoordinates data graph
  · exact terminal_eq_of_page ledgerCoordinates data graph

variable (coordinates : Coordinates source) (targets : TargetSection source) (desired : WholeSection source targets)

def graph (code : B) (tag : Nat) : Prop :=
  let head := MotherHigherLawFamily.unpair code
  let tail := MotherHigherLawFamily.unpair head.2
  ∃ point, coordinates.occurrence point = head.1 ∧
    page source ledgerCoordinates point.2 (source.toRootSource.actual.compile point.2)
      (targets point) (desired point) tag tail.1 tail.2

def reader (code : B) (tag : Nat) : ℝ :=
  if graph source ledgerCoordinates coordinates targets desired code tag then 0 else 1

theorem reader_bit {material : M}
    (hm : MotherHigherLawFormation.read material = reader source ledgerCoordinates coordinates targets desired)
    (code : B) (tag : Nat) : bit material tag code ↔ graph source ledgerCoordinates coordinates targets desired code tag := by
  by_cases seen : graph source ledgerCoordinates coordinates targets desired code tag <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

theorem point_graph {material : M}
    (hm : MotherHigherLawFormation.read material = reader source ledgerCoordinates coordinates targets desired)
    (point : Sigma source.toRootSource.actual.OccurrenceAt) (tag : Nat) (input output : B) :
    r3 material tag (coordinates.occurrence point) input output ↔
      page source ledgerCoordinates point.2 (source.toRootSource.actual.compile point.2)
        (targets point) (desired point) tag input output := by
  rw [r3, reader_bit source ledgerCoordinates coordinates targets desired hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, same, selected⟩
    have same := coordinates.occurrence.injective same
    cases same
    exact selected
  · intro selected
    exact ⟨point, rfl, selected⟩

theorem checked {material : M}
    (hm : MotherHigherLawFormation.read material = reader source ledgerCoordinates coordinates targets desired) :
    WholeSectionCheck coordinates ledgerCoordinates targets material := fun point =>
  checkOfPage source ledgerCoordinates point.2 (source.toRootSource.actual.compile point.2)
    (targets point) (desired point) (point_graph source ledgerCoordinates coordinates targets desired hm point)

theorem generated_eq {material : M}
    (hm : MotherHigherLawFormation.read material = reader source ledgerCoordinates coordinates targets desired) :
    generatedWhole coordinates ledgerCoordinates targets material
      (checked source ledgerCoordinates coordinates targets desired hm) = desired := by
  funext point
  exact whole_eq_of_page source ledgerCoordinates point.2 (source.toRootSource.actual.compile point.2)
    (targets point) (desired point) (point_graph source ledgerCoordinates coordinates targets desired hm point)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler.WholeEncoding
