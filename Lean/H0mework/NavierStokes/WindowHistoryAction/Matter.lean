import H0mework.NavierStokes.WindowSchurFirst.Jet
import H0mework.NavierStokes.WindowHistory.Mass

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWholeActionMatter
open MeasureTheory
open PhysicsCore.DiracCliffordRepresentation
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalGradient NativeWindowHistoryGNS
open NativeWindowHistoryGradient NativeWindowHistoryFirstJet
noncomputable section
variable {nu : Viscosity}

def assemble (background : HistoryHilbert) (components : Coordinate → HistoryHilbert) : Spinor :=
  !![0, 0; 0, 0;
    background+(1/4 : ℂ) • components 2,
      (1/4 : ℂ) • (components 0-Complex.I • components 1);
    (1/4 : ℂ) • (components 0+Complex.I • components 1),
      background-(1/4 : ℂ) • components 2]

theorem matter_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    matter seed time wave = assemble (constant (lp.single 2 wave (1 : ℂ)))
      (fun coordinate => history seed time (wave,coordinate)) := by
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [matter,mapSpinor,NativeHilbertDiracCurrent.matter,assemble,
      realization_background,realization_component,map_add,map_sub,map_smul]

def translate (wave : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) (field : Spinor) : Spinor :=
  fun spin color => NativeWindowHistoryTranslation.action wave direction displacement (field spin color)

theorem translate_assemble (wave : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (background : HistoryHilbert) (components : Coordinate → HistoryHilbert) :
    translate wave direction displacement (assemble background components) =
      assemble (NativeWindowHistoryTranslation.action wave direction displacement background)
        (fun coordinate => NativeWindowHistoryTranslation.action wave direction displacement (components coordinate)) := by
  funext spin color
  fin_cases spin <;> fin_cases color <;> simp [translate,assemble,map_add,map_sub,map_smul]

theorem translate_background (wave : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) :
    NativeWindowHistoryTranslation.action wave direction displacement (constant (lp.single 2 wave (1 : ℂ))) =
      constant (lp.single 2 wave (1 : ℂ)) := by
  rw [action_constant]
  congr 1
  apply lp.ext
  funext internal
  rw [NativeWindowHistoryTranslation.translation_apply]
  by_cases same : internal=wave
  · subst internal
    simp [NativeSpatialTranslation.phase,NativeSpatialTranslation.frequency]
  · simp [lp.single_apply,same]

theorem assemble_hasDerivAt {background : ℝ → HistoryHilbert} {backgroundJet : HistoryHilbert}
    {components : ℝ → Coordinate → HistoryHilbert} {componentJet : Coordinate → HistoryHilbert}
    (base : HasDerivAt background backgroundJet 0)
    (jets : ∀ coordinate, HasDerivAt (fun parameter => components parameter coordinate) (componentJet coordinate) 0) :
    HasDerivAt (fun parameter => assemble (background parameter) (components parameter))
      (assemble backgroundJet componentJet) 0 := by
  apply hasDerivAt_pi.mpr
  intro spin
  apply hasDerivAt_pi.mpr
  intro color
  fin_cases spin <;> fin_cases color
  all_goals simp only [assemble]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact base.add ((jets 2).const_smul (1/4 : ℂ))
  · exact ((jets 0).sub ((jets 1).const_smul Complex.I)).const_smul (1/4 : ℂ)
  · exact ((jets 0).add ((jets 1).const_smul Complex.I)).const_smul (1/4 : ℂ)
  · exact base.sub ((jets 2).const_smul (1/4 : ℂ))

def matterJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) : Spinor :=
  assemble 0 (fun coordinate => jet seed time valid (wave,coordinate) direction)

theorem matter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) :
    HasDerivAt (fun displacement => translate wave direction displacement (matter seed time wave))
      (matterJet seed time valid wave direction) 0 := by
  simp_rw [matter_original,translate_assemble,translate_background]
  exact assemble_hasDerivAt (hasDerivAt_const _ _) fun coordinate =>
    source_hasDerivAt seed time valid (wave,coordinate) direction

theorem translate_action (wave : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (matrix : DiracMatrix) (field : Spinor) :
    translate wave direction displacement (action matrix field) = action matrix (translate wave direction displacement field) := by
  funext spin color
  simp only [translate,action,map_sum,map_smul]

theorem action_hasDerivAt {path : ℝ → Spinor} {derivative : Spinor}
    (actual : HasDerivAt path derivative 0) (matrix : DiracMatrix) :
    HasDerivAt (fun parameter => action matrix (path parameter)) (action matrix derivative) 0 := by
  apply hasDerivAt_pi.mpr
  intro spin
  apply hasDerivAt_pi.mpr
  intro color
  convert! HasDerivAt.sum (u := Finset.univ) (fun other _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp actual other) color)).const_smul (matrix spin other)) using 1

theorem acted_matter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) (matrix : DiracMatrix) :
    HasDerivAt (fun displacement => translate wave direction displacement (action matrix (matter seed time wave)))
      (action matrix (matterJet seed time valid wave direction)) 0 := by
  simp_rw [translate_action]
  exact action_hasDerivAt (matter_hasDerivAt seed time valid wave direction) matrix

def fiber (field : Spinor) : NativeWindowWholeMass.HistoryFiber :=
  WithLp.toLp 2 fun entry => field entry.1 entry.2

theorem assemble_energy (components : Coordinate → HistoryHilbert) :
    ‖fiber (assemble 0 components)‖^2 = (1/8 : ℝ)*∑ coordinate, ‖components coordinate‖^2 := by
  have cancel := parallelogram_law_with_norm ℂ (components 0) (Complex.I • components 1)
  simp only [norm_smul,Complex.norm_I,one_mul] at cancel
  simp [fiber,PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,assemble,
    Fin.sum_univ_four,Fin.sum_univ_two,Fin.sum_univ_three,norm_smul]
  rw [← smul_add]
  rw [norm_smul]
  norm_num
  nlinarith

theorem normalized_mass (velocity : PhysicalSpace) (field : Spinor) :
    (∑ spin : Fin 4, ∑ color : Fin 2, inner ℂ (field spin color)
      (action (NativeCanonicalFriedrichsPrincipal.normalized velocity 0) field spin color)).re = ‖fiber field‖^2 := by
  simp [NativeCanonicalFriedrichsPrincipal.normalized_time,action,Matrix.one_apply,
    fiber,PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,Complex.re_sum,
    inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]

theorem matter_gradient_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) (velocity : PhysicalSpace) :
    (∑ spin : Fin 4, ∑ color : Fin 2, inner ℂ (matterJet seed time valid wave direction spin color)
      (action (NativeCanonicalFriedrichsPrincipal.normalized velocity 0)
        (matterJet seed time valid wave direction) spin color)).re =
      (1/8 : ℝ)*∑ coordinate, ‖jet seed time valid (wave,coordinate) direction‖^2 := by
  rw [normalized_mass,matterJet,assemble_energy]

theorem matter_gradient_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) :
    ‖fiber (matterJet seed time valid wave direction)‖^2 ≤
      (3/8 : ℝ)*(2*Real.pi)^2*ceiling*
        NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  rw [matterJet,assemble_energy]
  have paid := Finset.sum_le_sum fun coordinate (_ : coordinate ∈ Finset.univ) =>
    jet_bound seed time valid (wave,coordinate) direction
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,nsmul_eq_mul] at paid
  nlinarith

theorem matter_gradient_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) :
    ‖fiber (matterJet seed time valid wave direction)‖^2 =
      ‖fiber (assemble 0 fun coordinate => constant (meanJet seed time valid (wave,coordinate) direction))‖^2+
      ‖fiber (assemble 0 fun coordinate => centeredJet seed time valid (wave,coordinate) direction)‖^2 := by
  simp only [matterJet,assemble_energy,gradient_energy_split]
  have same (coordinate : Coordinate) : ‖constant (meanJet seed time valid (wave,coordinate) direction)‖ =
      ‖meanJet seed time valid (wave,coordinate) direction‖ := constantIsometry.norm_map _
  simp only [same,Finset.sum_add_distrib,mul_add]

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem matterJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) (direction : Coordinate) :
    matterJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) wave direction =
      matterJet step.1 time (by linarith) wave direction := by
  simp only [matterJet,jet_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowWholeActionMatter
