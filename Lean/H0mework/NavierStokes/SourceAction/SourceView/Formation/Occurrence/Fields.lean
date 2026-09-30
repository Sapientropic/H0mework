import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.NavierStokes.Restart.NativeAccumulationRoot

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherOccurrenceMaterial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open PhysicsCore.StageNineCanonicalCauchyState
noncomputable section
variable {nu : Viscosity}
variable {seed : GeneratedWholeRestartCurrent nu}

abbrev Occurrence (seed : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent seed) :=
  (nativeTemporalSource seed).toRootSource.actual.OccurrenceAt current

abbrev Anchor (seed : GeneratedWholeRestartCurrent nu) := Σ current : NativeTemporalCurrent seed,Occurrence seed current

def sourceClock (seed : GeneratedWholeRestartCurrent nu) : NativeTemporalCurrent seed → ℝ
  | .finite stage => GeneratedWholeRestartCurrent.elapsedTime seed stage
  | .cofinal => wholeRestartVelocityAccumulationTime seed
  | .galerkin _ => wholeRestartVelocityAccumulationTime seed

structure Query where
  time : ℝ
  radius : ℕ
  order : ℕ

abbrev Input (seed : GeneratedWholeRestartCurrent nu) := Anchor seed × Query
abbrev Row := IntegerWavevector → Coordinate → ℂ
abbrev Address := IntegerWavevector × Coordinate × Bool
noncomputable instance addressCodec : Encodable Address := Encodable.ofCountable Address

def rowSample (value : Row) (index : ℕ) : ℝ :=
  match Encodable.decode (α := Address) index with
  | none => 0
  | some (wave,coordinate,part) => if part then (value wave coordinate).im else (value wave coordinate).re

theorem rowSample_injective : Function.Injective rowSample := by
  intro first last same
  funext wave coordinate
  apply Complex.ext
  · have h:=congrFun same (Encodable.encode (wave,coordinate,false))
    simpa only [rowSample,Encodable.encodek,Bool.false_eq_true,↓reduceIte] using h
  · have h:=congrFun same (Encodable.encode (wave,coordinate,true))
    simpa only [rowSample,Encodable.encodek,↓reduceIte] using h

def endpointRow (value : WholeRestartVelocityEndpointState) : Row :=
  fun wave coordinate => if nonzero : wave≠0 then value ⟨wave,nonzero⟩ coordinate else 0

theorem endpointRow_injective : Function.Injective endpointRow := by
  intro first last same
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  have h:=congrFun (congrFun same wave.val) coordinate
  have nonzero : wave.val≠0 := wave.property
  simpa only [endpointRow,dif_pos nonzero] using h

def currentCode (seed : GeneratedWholeRestartCurrent nu) : NativeTemporalCurrent seed → ℕ
  | .finite stage => 3*stage
  | .cofinal => 1
  | .galerkin radius => 3*radius+2

theorem currentCode_injective (seed : GeneratedWholeRestartCurrent nu) : Function.Injective (currentCode seed) := by
  intro first last same
  cases first <;> cases last <;> simp only [currentCode] at same <;> congr 1 <;> omega

def cofinalSample (receipt : GeneratedWholeRestartCanonicalWeakCofinalReceiptAt seed)
    (parameter : ℝ) (index : ℕ) : ℝ :=
  if parameter=0 then rowSample (endpointRow receipt.kineticEndpoint) index
  else if parameter=1 then rowSample (endpointRow receipt.velocityEndpoint) index
  else (receipt.subsequence index : ℝ)

theorem cofinalSample_injective (seed : GeneratedWholeRestartCurrent nu) :
    Function.Injective (cofinalSample (seed := seed)) := by
  intro first last same
  have kinetic:first.kineticEndpoint=last.kineticEndpoint := by
    apply endpointRow_injective
    apply rowSample_injective
    exact funext fun index => by simpa only [cofinalSample,↓reduceIte] using congrFun (congrFun same 0) index
  have velocity:first.velocityEndpoint=last.velocityEndpoint := by
    apply endpointRow_injective
    apply rowSample_injective
    exact funext fun index => by simpa only [cofinalSample,one_ne_zero,↓reduceIte] using congrFun (congrFun same 1) index
  have subsequence:first.subsequence=last.subsequence := by
    funext index
    have actual:=congrFun (congrFun same 2) index
    norm_num only [cofinalSample,OfNat.ofNat_ne_zero,show (2:ℝ)≠1 by norm_num,↓reduceIte] at actual
    exact Nat.cast_injective actual
  cases first
  cases last
  cases kinetic
  cases velocity
  cases subsequence
  rfl

def observation (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) (parameter : ℝ) (index : ℕ) : ℝ :=
  match anchor with
  | ⟨.finite _,⟨_,.finite _ _⟩⟩ => 0
  | ⟨.cofinal,⟨_,.cofinal receipt⟩⟩ => cofinalSample receipt parameter index
  | ⟨.galerkin _,⟨_,.galerkin _ write⟩⟩ => rowSample (write.trajectory parameter) index

private theorem finite_occurrence_unique (seed : GeneratedWholeRestartCurrent nu) (index : ℕ)
    (first last : GeneratedWholeRestartNativeActualOccurrenceAt seed index) : first=last := by
  have same:first.response=last.response:=Option.some.inj (first.generated.symm.trans last.generated)
  cases first
  cases last
  cases same
  rfl

theorem occurrence_recovered (seed : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent seed)
    (first last : Occurrence seed current)
    (same : observation seed ⟨current,first⟩=observation seed ⟨current,last⟩) : first=last := by
  rcases first with ⟨support,first⟩
  cases first with
  | finite index first =>
    rcases last with ⟨support,last⟩
    cases last with
    | finite _ last =>
      cases finite_occurrence_unique seed index first last
      rfl
  | cofinal first =>
    rcases last with ⟨support,last⟩
    cases last with
    | cofinal last =>
      cases cofinalSample_injective seed same
      rfl
  | galerkin radius first =>
    rcases last with ⟨support,last⟩
    cases last with
    | galerkin _ last =>
      have trajectory:first.trajectory=last.trajectory := by
        funext parameter
        apply lp.ext
        exact rowSample_injective (congrFun same parameter)
      have equal:first=last := by
        cases first
        cases last
        cases trajectory
        rfl
      cases equal
      rfl

-- Raw real-point material preserves the whole trajectory, including its values outside [0,1].
def rawState (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) : StageNineCauchyState where
  coframe point row column := if row=0 ∧ column=0 then observation seed anchor (point 0) (Nat.floor (point 1)) else 0
  gravityConnection := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := 0
  gaugeAuxiliary := 0
  scalar := 0
  scalarVelocity := 0
  matter := 0
  conjugateMatter := 0

def samplePoint (parameter : ℝ) (index : ℕ) : StageNineSpatialPoint := WithLp.toLp 2 ![parameter,(index:ℝ),0]

theorem rawState_read (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) (parameter : ℝ) (index : ℕ) :
    (rawState seed anchor).coframe (samplePoint parameter index) 0 0=observation seed anchor parameter index := by
  simp [rawState,samplePoint]

end
end SaturationMonoid.NavierStokes.NativeWindowMotherOccurrenceMaterial
