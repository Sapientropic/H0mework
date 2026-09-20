import H0mework.Physics.MotherDeclarationsPhysical.CurrentInput

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent

open CurrentMaterial StageNineCanonicalCauchyState StageNineHolonomicField StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction SU7MotherLieAlgebra

noncomputable section

local instance instFiniteRealP286LieBlockData_scratch : Module.Finite ℝ P286LieBlockData := ActualInitial.p286ModuleFinite
local instance instFintypeP286CoordinateIndex_scratch : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance instFintypeMatterCoordinateIndex_scratch : Fintype MatterCoordinateIndex := Fintype.ofFinite _

def readComplex (law : MotherPointwiseLaws.Law) (channel : Bool → Channel)
    (point : StageNineSpatialPoint) : ℂ :=
  ⟨readReal law (channel false) point, readReal law (channel true) point⟩

/-- Fixed coordinate inverses restore every original raw field from full real-point evaluation. -/
def readInitial (law : MotherPointwiseLaws.Law) : StageNineCauchyState where
  coframe := fun point row column => readReal law (.coframe row column) point
  gravityConnection := fun point direction row column => readReal law (.gravityConnection direction row column) point
  gravityAuxiliary := fun point internalPair spacetimePair => readReal law (.gravityAuxiliary internalPair spacetimePair) point
  gravitySimplicityMultiplier := fun point internalPair spacetimePair => readReal law (.gravityMultiplier internalPair spacetimePair) point
  gaugeConnection := fun point direction => p286CoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => readReal law (.gaugeConnection direction coordinate) point))
  gaugeAuxiliary := fun point pair => p286CoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => readReal law (.gaugeAuxiliary pair coordinate) point))
  scalar := fun point => WithLp.toLp 2 (fun coordinate => readComplex law (.scalar coordinate) point)
  scalarVelocity := fun point => WithLp.toLp 2 (fun coordinate => readComplex law (.scalarVelocity coordinate) point)
  matter := fun point => matterCoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => readComplex law (.matter coordinate) point))
  conjugateMatter := fun point => coordinateDual (fun coordinate => readComplex law (.dual coordinate) point)

def readCurrent (law : MotherPointwiseLaws.Law) : StageNineCauchyState × ℝ :=
  (readInitial law, readReal law .clock 0)

theorem initial_recovered (law : MotherPointwiseLaws.Law) (initial : StageNineCauchyState) (clock : ℝ)
    (formed : readReal law = observe initial clock) : readInitial law = initial := by
  unfold readInitial readComplex
  rw [formed]
  simp only [observe, complexPart, Bool.false_eq_true, ↓reduceIte]
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point direction
    exact p286CoordinateEquiv.symm_apply_apply _
  · funext point pair
    exact p286CoordinateEquiv.symm_apply_apply _
  · rfl
  · rfl
  · funext point
    exact matterCoordinateEquiv.symm_apply_apply _
  · funext point
    exact coordinateDual_recovers _

/-- No regularity hypothesis is needed: the law reads all real points simultaneously. -/
theorem every_current (current : StageNineCauchyState × ℝ) :
    ∃ law : MotherPointwiseLaws.Law,
      readReal law = observe current.1 current.2 ∧ readCurrent law = current := by
  obtain ⟨law, formed⟩ := MotherPointwiseLaws.every_restriction inputSamples inputSamples_injective
    (fun input => fun _ => observe current.1 current.2 input.2 input.1)
  have reads : readReal law = observe current.1 current.2 := by
    funext channel point
    exact congrFun (formed (point, channel)) 0
  exact ⟨law, reads, Prod.ext (initial_recovered law current.1 current.2 reads)
    (by change readReal law .clock 0 = current.2; rw [reads]; rfl)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent
