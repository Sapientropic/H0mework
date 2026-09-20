import H0mework.Physics.MotherProgrammesFormationCurrent.Spatial

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial

open StageNineCanonicalCauchyState StageNineHolonomicField StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction StageNineCoframeLocalDifferentiability SU7MotherLieAlgebra

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  ActualInitial.p286ModuleFinite

local instance p286CoordinateFintype : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance matterCoordinateFintype : Fintype MatterCoordinateIndex := Fintype.ofFinite _

inductive Channel
  | coframe (row column : Fin 4)
  | gravityConnection (direction row column : Fin 4)
  | gravityAuxiliary (internalPair spacetimePair : Fin 6)
  | gravityMultiplier (internalPair spacetimePair : Fin 6)
  | gaugeConnection (direction : Fin 4) (coordinate : P286CoordinateIndex)
  | gaugeAuxiliary (pair : Fin 6) (coordinate : P286CoordinateIndex)
  | scalar (coordinate : ScalarBasisIndex) (imaginary : Bool)
  | scalarVelocity (coordinate : ScalarBasisIndex) (imaginary : Bool)
  | matter (coordinate : MatterCoordinateIndex) (imaginary : Bool)
  | dual (coordinate : MatterCoordinateIndex) (imaginary : Bool)
  | clock
  deriving Fintype

def complexPart (imaginary : Bool) (value : ℂ) : ℝ :=
  if imaginary then value.im else value.re

theorem complexPart_continuous (imaginary : Bool) : Continuous (complexPart imaginary) := by
  cases imaginary
  · exact Complex.continuous_re
  · exact Complex.continuous_im

def observe (initial : StageNineCauchyState) (clock : ℝ) :
    Channel → StageNineSpatialPoint → ℝ
  | .coframe row column, point => initial.coframe point row column
  | .gravityConnection direction row column, point => initial.gravityConnection point direction row column
  | .gravityAuxiliary internalPair spacetimePair, point => initial.gravityAuxiliary point internalPair spacetimePair
  | .gravityMultiplier internalPair spacetimePair, point => initial.gravitySimplicityMultiplier point internalPair spacetimePair
  | .gaugeConnection direction coordinate, point => p286CoordinateEquiv (initial.gaugeConnection point direction) coordinate
  | .gaugeAuxiliary pair coordinate, point => p286CoordinateEquiv (initial.gaugeAuxiliary point pair) coordinate
  | .scalar coordinate imaginary, point => complexPart imaginary (initial.scalar point coordinate)
  | .scalarVelocity coordinate imaginary, point => complexPart imaginary (initial.scalarVelocity point coordinate)
  | .matter coordinate imaginary, point => complexPart imaginary (matterCoordinateEquiv (initial.matter point) coordinate)
  | .dual coordinate imaginary, point => complexPart imaginary (initial.conjugateMatter point
      (matterCoordinateEquiv.symm (EuclideanSpace.single coordinate 1)))
  | .clock, _ => clock

theorem observe_continuous (initial : StageNineCauchyState) (clock : ℝ)
    (smooth : ActualInitial.SmoothInitial initial) (channel : Channel) :
    Continuous (observe initial clock channel) := by
  cases channel with
  | coframe row column => exact (smooth.coframe row column).continuous
  | gravityConnection direction row column => exact (smooth.gravityConnection direction row column).continuous
  | gravityAuxiliary internalPair spacetimePair => exact (smooth.gravityAuxiliary internalPair spacetimePair).continuous
  | gravityMultiplier internalPair spacetimePair => exact (smooth.gravitySimplicityMultiplier internalPair spacetimePair).continuous
  | gaugeConnection direction coordinate =>
      exact (PiLp.continuous_apply 2 _ coordinate).comp (smooth.gaugeConnection direction).continuous
  | gaugeAuxiliary pair coordinate =>
      exact (PiLp.continuous_apply 2 _ coordinate).comp (smooth.gaugeAuxiliary pair).continuous
  | scalar coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp smooth.scalar.continuous)
  | scalarVelocity coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp smooth.scalarVelocity.continuous)
  | matter coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp smooth.matter.continuous)
  | dual coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp (smooth.conjugateMatter coordinate).continuous
  | clock => exact continuous_const

/-- The independent dual is reconstructed from all of its original basis evaluations. -/
def coordinateDual (coefficients : MatterCoordinateIndex → ℂ) :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun matter := ∑ index, matterCoordinateEquiv matter index * coefficients index
  map_add' := by
    intro first second
    simp only [map_add, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar matter
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, Finset.mul_sum]

theorem coordinateDual_recovers (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    coordinateDual (fun index => dual
      (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) = dual := by
  apply LinearMap.ext
  intro matter
  exact (coframeMatterDual_coordinate_expansion dual (matterCoordinateEquiv matter)).symm.trans
    (congrArg dual (matterCoordinateEquiv.symm_apply_apply matter))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial
