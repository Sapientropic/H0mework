import H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source

/-! Any ordered finite gauge word consumes complete original Dirac propagators. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

structure GaugeLine where
  configuration : StageNineHolonomicConfiguration
  point : BasePoint
  momentum : Fin 3 → ℝ
  energy : ℂ
  direction : LorentzianIndex
  gauge : P286LieBlockData

def GaugeLine.full (line : GaugeLine) : Mother :=
  Triangular.diracResolvent line.configuration line.point line.momentum line.energy *
    Exchange.currentOperator (line.configuration.coframe line.point) line.direction line.gauge

def GaugeLine.diagonal (line : GaugeLine) : Mother :=
  freeDiracResolvent line.configuration line.point line.momentum line.energy *
    Exchange.currentOperator (line.configuration.coframe line.point) line.direction line.gauge

def GaugeLine.Regular (line : GaugeLine) : Prop :=
  coframeTemporalPrincipalScalar (line.configuration.coframe line.point)≠0 ∧
    IsUnit (Triangular.freeKernel line.configuration line.point line.momentum line.energy)

theorem GaugeLine.propagator (line : GaugeLine) (regular : line.Regular) :
    Triangular.diracKernel line.configuration line.point line.momentum line.energy *
      Triangular.diracResolvent line.configuration line.point line.momentum line.energy=1 ∧
    Triangular.diracResolvent line.configuration line.point line.momentum line.energy *
      Triangular.diracKernel line.configuration line.point line.momentum line.energy=1 :=
  Triangular.diracResolvent_two_sided line.configuration line.point line.momentum line.energy regular.1 regular.2

theorem GaugeLine.generated (line : GaugeLine) (regular : line.Regular) :
    Expansion line.full line.diagonal :=
  (source_diracResolvent line.configuration line.point line.momentum line.energy regular.2).mul
    (original_gauge_vertex (line.configuration.coframe line.point) line.direction line.gauge)

theorem gauge_word_generated (lines : List GaugeLine)
    (regular : ∀ line ∈ lines, line.Regular) :
    Expansion (lines.map GaugeLine.full).prod (lines.map GaugeLine.diagonal).prod := by
  have generated := Expansion.product (lines.map fun line => (line.full,line.diagonal)) (by
    intro pair member
    rcases List.mem_map.mp member with ⟨line,member,equality⟩
    rw [← equality]
    exact line.generated (regular line member))
  simpa only [List.map_map,Function.comp_def] using generated

theorem gauge_loop_independent_yukawa (lines : List GaugeLine)
    (regular : ∀ line ∈ lines, line.Regular) :
    loopTrace (lines.map GaugeLine.full).prod=loopTrace (lines.map GaugeLine.diagonal).prod :=
  expansion_trace (gauge_word_generated lines regular)

theorem scalar_insertion_closed_loop (before after : List GaugeLine)
    (regularBefore : ∀ line ∈ before, line.Regular)
    (regularAfter : ∀ line ∈ after, line.Regular) (scalar : ScalarCoordinateCarrier) :
    loopTrace ((before.map GaugeLine.full).prod *
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar) *
        (after.map GaugeLine.full).prod)=0 :=
  arrow_trace (Expansion.arrow_right
    ((gauge_word_generated before regularBefore).arrow_left (original_scalar_vertex scalar))
    (gauge_word_generated after regularAfter))

theorem two_scalar_open_chain (first second : ScalarCoordinateCarrier)
    (lines : List GaugeLine) (regular : ∀ line ∈ lines, line.Regular) :
    diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm first) *
      (lines.map GaugeLine.full).prod *
        diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm second)=0 :=
  (Expansion.arrow_right (original_scalar_vertex first) (gauge_word_generated lines regular)).compose_zero
    (original_scalar_vertex second)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
