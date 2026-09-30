import H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words
import H0mework.Physics.LowEnergy.FullQuantum.Retarded.Original

/-! Original positive-damping lines generate the source-prepared weighted word, without caller inverse certificates. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
open ClosedLoops StateGreen CoframeResponse Triangular
open YangMills.FullPairing DiracExteriorMatterAction ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

structure SourceStep where
  momentum : Fin 3 → ℝ
  energy : ℝ
  damping : ℝ
  positive : 0<damping
  direction : LorentzianIndex
  gauge : P286LieBlockData

def SourceStep.line (point : BasePoint) (step : SourceStep) : GaugeLine where
  configuration := actual
  point := point
  momentum := step.momentum
  energy := Retarded.spectralParameter step.energy step.damping
  direction := step.direction
  gauge := step.gauge

theorem SourceStep.regular (point : BasePoint) (step : SourceStep) : (step.line point).Regular :=
  ⟨actual_noncharacteristic point,Retarded.sourceFree_regular point step.momentum step.energy step.damping step.positive⟩

def fullSteps (point : BasePoint) (steps : List SourceStep) : List Mother :=
  steps.map fun step => (step.line point).full

def diagonalSteps (point : BasePoint) (steps : List SourceStep) : List Mother :=
  steps.map fun step => (step.line point).diagonal

theorem steps_generated (point : BasePoint) (steps : List SourceStep) :
    Expansion (fullSteps point steps).prod (diagonalSteps point steps).prod := by
  have generated := gauge_word_generated (steps.map fun step => step.line point) (by
    intro line member
    rcases List.mem_map.mp member with ⟨step,_,rfl⟩
    exact step.regular point)
  simpa only [fullSteps,diagonalSteps,List.map_map,Function.comp_def] using generated

theorem source_weighted_yukawa_independent (point : BasePoint) (steps : List SourceStep) :
    read (preparedVector point) (weightedWord actual point (fullSteps point steps))=
      read (preparedVector point) (weightedWord actual point (diagonalSteps point steps)) := by
  simp only [weightedWord,fullWord_read,List.prod_cons]
  exact weighted_expansion point actual point _ _ (steps_generated point steps)

theorem source_scalar_weighted_word (point : BasePoint) (before after : List SourceStep)
    (scalar : ScalarCoordinateCarrier) :
    read (preparedVector point) (weightedWord actual point
      (fullSteps point before++diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar)::fullSteps point after))=0 := by
  have arrow := Expansion.arrow_right
    ((steps_generated point before).arrow_left (original_scalar_vertex scalar)) (steps_generated point after)
  have zero := weighted_arrow_zero point actual point _ arrow
  simpa only [weightedWord,fullWord_read,List.prod_cons,List.prod_append,mul_assoc] using zero

theorem source_weighted_Stage10 (point : BasePoint) (steps : List SourceStep) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
        (sourceWordMother (weightedWord actual point (fullSteps point steps)))))=
      read (preparedVector point) (weightedWord actual point (diagonalSteps point steps)) := by
  rw [weightedWord_native,source_weighted_yukawa_independent]

theorem source_scalar_Stage10 (point : BasePoint) (before after : List SourceStep)
    (scalar : ScalarCoordinateCarrier) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
        (sourceWordMother (weightedWord actual point
          (fullSteps point before++diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar)::fullSteps point after)))))=0 := by
  rw [weightedWord_native,source_scalar_weighted_word]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
