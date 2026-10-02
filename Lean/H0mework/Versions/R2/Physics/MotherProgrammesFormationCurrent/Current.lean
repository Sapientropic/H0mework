import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.Coordinates
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial

open StageNineCanonicalCauchyState StageNineHolonomicField StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction SU7MotherLieAlgebra

noncomputable section

attribute [local instance] p286ModuleFinite p286CoordinateFintype matterCoordinateFintype

abbrev Query := RationalPoint × Channel
noncomputable instance : Encodable Query := Encodable.ofCountable Query

def currentSamples (initial : StageNineCauchyState) (clock : ℝ) : ℕ → ℝ :=
  fun address => match Encodable.decode (α := Query) address with
    | none => 0
    | some query => observe initial clock query.2 (rationalPoint query.1)

def readSample (material : MotherStreamFormation.Carrier) (channel : Channel)
    (point : RationalPoint) : ℝ :=
  MotherStreamFormation.read material (Encodable.encode (point, channel))

def decodeReal (material : MotherStreamFormation.Carrier) (channel : Channel) :
    StageNineSpatialPoint → ℝ := extendReal (readSample material channel)

def decodeComplex (material : MotherStreamFormation.Carrier) (channel : Bool → Channel)
    (point : StageNineSpatialPoint) : ℂ :=
  ⟨decodeReal material (channel false) point, decodeReal material (channel true) point⟩

/-- All primitive fields are calculated from this one source value's rational spatial samples. -/
def decodeInitial (material : MotherStreamFormation.Carrier) : StageNineCauchyState where
  coframe := fun point row column => decodeReal material (.coframe row column) point
  gravityConnection := fun point direction row column => decodeReal material (.gravityConnection direction row column) point
  gravityAuxiliary := fun point internalPair spacetimePair => decodeReal material (.gravityAuxiliary internalPair spacetimePair) point
  gravitySimplicityMultiplier := fun point internalPair spacetimePair => decodeReal material (.gravityMultiplier internalPair spacetimePair) point
  gaugeConnection := fun point direction => p286CoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => decodeReal material (.gaugeConnection direction coordinate) point))
  gaugeAuxiliary := fun point pair => p286CoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => decodeReal material (.gaugeAuxiliary pair coordinate) point))
  scalar := fun point => WithLp.toLp 2 (fun coordinate => decodeComplex material (.scalar coordinate) point)
  scalarVelocity := fun point => WithLp.toLp 2 (fun coordinate => decodeComplex material (.scalarVelocity coordinate) point)
  matter := fun point => matterCoordinateEquiv.symm
    (WithLp.toLp 2 (fun coordinate => decodeComplex material (.matter coordinate) point))
  conjugateMatter := fun point => coordinateDual
    (fun coordinate => decodeComplex material (.dual coordinate) point)

def decodeClock (material : MotherStreamFormation.Carrier) : ℝ :=
  readSample material .clock (fun _ => 0)

def decodeCurrent (material : MotherStreamFormation.Carrier) : StageNineCauchyState × ℝ :=
  (decodeInitial material, decodeClock material)

theorem decodeReal_recovers (initial : StageNineCauchyState) (clock : ℝ)
    (smooth : ActualInitial.SmoothInitial initial) {material : MotherStreamFormation.Carrier}
    (formed : MotherStreamFormation.read material = currentSamples initial clock) (channel : Channel) :
    decodeReal material channel = observe initial clock channel := by
  unfold decodeReal readSample
  rw [formed]
  simp only [currentSamples, Encodable.encodek]
  exact extendReal_recovers _ (observe_continuous initial clock smooth channel)

theorem decodeInitial_recovers (initial : StageNineCauchyState) (clock : ℝ)
    (smooth : ActualInitial.SmoothInitial initial) {material : MotherStreamFormation.Carrier}
    (formed : MotherStreamFormation.read material = currentSamples initial clock) :
    decodeInitial material = initial := by
  unfold decodeInitial decodeComplex
  simp_rw [decodeReal_recovers initial clock smooth formed]
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

theorem decodeClock_recovers (initial : StageNineCauchyState) (clock : ℝ)
    {material : MotherStreamFormation.Carrier}
    (formed : MotherStreamFormation.read material = currentSamples initial clock) :
    decodeClock material = clock := by
  simp only [decodeClock, readSample, formed, currentSamples, Encodable.encodek, observe]

/-- The single formation witness restores all ten fields and the independent current clock. -/
theorem entire_current_formed (initial : StageNineCauchyState) (clock : ℝ)
    (smooth : ActualInitial.SmoothInitial initial) :
    ∃ material : MotherStreamFormation.Carrier,
      MotherStreamFormation.read material = currentSamples initial clock ∧
      decodeCurrent material = (initial, clock) := by
  obtain ⟨material, formed⟩ := MotherStreamFormation.read_surjective (currentSamples initial clock)
  exact ⟨material, formed, Prod.ext (decodeInitial_recovers initial clock smooth formed)
    (decodeClock_recovers initial clock formed)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial
