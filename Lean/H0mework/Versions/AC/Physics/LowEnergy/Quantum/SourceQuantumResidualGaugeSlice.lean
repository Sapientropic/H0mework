import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceQuantumScalarOrbitDimensions
import H0mework.Physics.SpinPair.ColorAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual source spatial connections generate the residual gauge orbit.
The native orthogonal slice is a linear carrier at that same source point.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceQuantumResidualGaugeSlice

open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField
open StageNineCoframeGravityGaugeRegularity Stage9C.Material.SpinPair
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumScalarOrbitDimensions
open SourceQuantumConfigurationHilbert
open scoped RealInnerProductSpace

def colorGenerator (i : Fin 3) : NativeLie := p286CoordinateEquiv (sourceColorP286Generator i)

def colorCombination : (Fin 3 → ℝ) →ₗ[ℝ] NativeLie where
  toFun x := ∑ i, x i • colorGenerator i
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, smul_smul]

theorem colorGenerator_coordinates (i : Fin 3) : nativeCoordinates (colorGenerator i) =
    ![(![0,1/2,0,0,0,0,0,0],0,0),(![1/2,0,0,0,0,0,0,0],0,0),
      (![0,0,0,0,0,0,1/2,0],0,0)] i := by
  rw [colorGenerator, nativeCoordinates_apply]
  simp only [sourceColorP286Generator_color, sourceColorP286Generator_weak_zero,
    sourceColorP286Generator_hypercharge_zero]
  fin_cases i <;> ext j
  all_goals try fin_cases j
  all_goals norm_num [sourceColorRaw, Matrix.cons_val_two]

theorem colorCombination_coordinates (x : Fin 3 → ℝ) :
    nativeCoordinates (colorCombination x) = (![x 1/2,x 0/2,0,0,0,0,x 2/2,0],0,0) := by
  change nativeCoordinates (∑ i : Fin 3, x i • colorGenerator i) = _
  rw [map_sum]
  simp_rw [map_smul, colorGenerator_coordinates]
  simp [Fin.sum_univ_three, div_eq_mul_inv, mul_comm]

private theorem colorCombination_injective : Function.Injective colorCombination := by
  intro x y h
  have hr := congrArg nativeCoordinates h
  rw [colorCombination_coordinates, colorCombination_coordinates] at hr
  have h0 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 1) hr
  have h1 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 0) hr
  have h2 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 6) hr
  simp at h0 h1 h2
  ext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem colorGenerator_mem (i : Fin 3) : colorGenerator i ∈ stabilizer := by
  change scalarMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator i))))
    (StageNineDynamicBreakingVacuum.sourceGeneratedVacuumCoordinates
      StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource) = 0
  rw [p286CoordinateEquiv.symm_apply_apply]
  exact sourceColorP286Generator_vacuum_zero i

def colorStabilizer : (Fin 3 → ℝ) →ₗ[ℝ] stabilizer :=
  colorCombination.codRestrict stabilizer (fun x =>
    stabilizer.sum_mem (fun i _ => stabilizer.smul_mem (x i) (colorGenerator_mem i)))

private theorem colorStabilizer_injective : Function.Injective colorStabilizer := by
  intro x y h
  exact colorCombination_injective (congrArg Subtype.val h)

/-- The original three source generators parametrize the full vacuum stabilizer. -/
def colorStabilizerEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] stabilizer :=
  colorStabilizer.linearEquivOfInjective colorStabilizer_injective (by rw [stabilizer_finrank]; simp)

def gaugeCoordinates : Gauge ≃ₗ[ℝ] (Fin 3 → NativeLie) :=
  WithLp.linearEquiv 2 ℝ (Fin 3 → NativeLie)

def sourceGauge : Gauge := WithLp.toLp 2
  (fun i : Fin 3 => p286CoordinateEquiv (actual.gaugeConnection 0 i.succ))

theorem sourceGauge_apply (i : Fin 3) : gaugeCoordinates sourceGauge i = gaugeScale • colorGenerator i := by
  change p286CoordinateEquiv (gaugePotential gaugeScale i.succ) = _
  have h : gaugePotential gaugeScale i.succ = gaugeScale • sourceColorP286Generator i := by
    fin_cases i <;> rfl
  rw [h, map_smul]
  rfl

def residualOrbit : stabilizer →ₗ[ℝ] Gauge where
  toFun a := WithLp.toLp 2 (fun i => jointP286CoordinateLieBracket (a : NativeLie) (gaugeCoordinates sourceGauge i))
  map_add' a b := by
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_add_left (a : NativeLie) (b : NativeLie) (gaugeCoordinates sourceGauge i)
  map_smul' r a := by
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_smul_left r (a : NativeLie) (gaugeCoordinates sourceGauge i)

theorem colorGenerator_bracket (i j : Fin 3) :
    jointP286CoordinateLieBracket (colorGenerator i) (colorGenerator j) =
      (!![0,-colorGenerator 2,colorGenerator 1;
          colorGenerator 2,0,-colorGenerator 0;
          -colorGenerator 1,colorGenerator 0,0] : Matrix (Fin 3) (Fin 3) NativeLie) i j := by
  unfold jointP286CoordinateLieBracket colorGenerator
  rw [p286CoordinateEquiv.symm_apply_apply, p286CoordinateEquiv.symm_apply_apply,
    sourceColorP286Generator_bracket]
  fin_cases i <;> fin_cases j <;> simp
  all_goals rfl


private theorem nativeBracket_smul_left (r : ℝ) (a b : NativeLie) :
    jointP286CoordinateLieBracket (r • a) b = r • jointP286CoordinateLieBracket a b :=
  jointP286CoordinateLieBracket_smul_left r a b

set_option backward.isDefEq.respectTransparency false in
theorem residualOrbit_color (x : Fin 3 → ℝ) (i : Fin 3) :
    gaugeCoordinates (residualOrbit (colorStabilizer x)) i =
      gaugeScale •
        ((![(x 1) • colorGenerator 2 - (x 2) • colorGenerator 1,
          (x 2) • colorGenerator 0 - (x 0) • colorGenerator 2,
          (x 0) • colorGenerator 1 - (x 1) • colorGenerator 0] : Fin 3 → NativeLie) i) := by
  change jointP286CoordinateLieBracket (colorCombination x) (gaugeCoordinates sourceGauge i) = _
  rw [sourceGauge_apply, jointP286CoordinateLieBracket_smul_right]
  congr 1
  change jointP286CoordinateLieBracket (∑ j : Fin 3, x j • colorGenerator j) (colorGenerator i) = _
  rw [Fin.sum_univ_three]
  simp only [jointP286CoordinateLieBracket_add_left,
    nativeBracket_smul_left, colorGenerator_bracket]
  fin_cases i <;> simp [sub_eq_add_neg]
  all_goals exact add_comm _ _

def orbitRows : Gauge →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![(nativeCoordinates (gaugeCoordinates v 1)).1 6,
    (nativeCoordinates (gaugeCoordinates v 0)).1 6,
    (nativeCoordinates (gaugeCoordinates v 0)).1 0]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

theorem residualOrbit_minor_action (x : Fin 3 → ℝ) :
    orbitRows (residualOrbit (colorStabilizer x)) =
      ![-gaugeScale / 2 * x 0, gaugeScale / 2 * x 1, -gaugeScale / 2 * x 2] := by
  ext i
  fin_cases i <;>
    simp [orbitRows, residualOrbit_color, map_sub, map_smul, colorGenerator_coordinates] <;> ring

/-- Three actual gauge-coordinate rows on the original source color basis. -/
def sourceOrbitMinor : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => orbitRows (residualOrbit (colorStabilizer (Pi.single j 1))) i

theorem sourceOrbitMinor_eq : sourceOrbitMinor =
    Matrix.diagonal ![-gaugeScale/2,gaugeScale/2,-gaugeScale/2] := by
  ext i j
  unfold sourceOrbitMinor
  rw [residualOrbit_minor_action]
  fin_cases i <;> fin_cases j <;> simp

theorem sourceOrbitMinor_det : sourceOrbitMinor.det = gaugeScale^3 / 8 := by
  rw [sourceOrbitMinor_eq, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]
  ring

theorem sourceOrbitMinor_det_pos : 0 < sourceOrbitMinor.det := by
  rw [sourceOrbitMinor_det]
  exact div_pos (pow_pos gaugeScale_pos 3) (by norm_num)

theorem residualOrbit_injective : Function.Injective residualOrbit := by
  intro a b h
  obtain ⟨x, rfl⟩ := colorStabilizerEquiv.surjective a
  obtain ⟨y, rfl⟩ := colorStabilizerEquiv.surjective b
  have hr := congrArg orbitRows h
  change orbitRows (residualOrbit (colorStabilizer x)) =
    orbitRows (residualOrbit (colorStabilizer y)) at hr
  rw [residualOrbit_minor_action, residualOrbit_minor_action] at hr
  have h0 := congrFun hr 0
  have h1 := congrFun hr 1
  have h2 := congrFun hr 2
  change -gaugeScale / 2 * x 0 = -gaugeScale / 2 * y 0 at h0
  change gaugeScale / 2 * x 1 = gaugeScale / 2 * y 1 at h1
  change -gaugeScale / 2 * x 2 = -gaugeScale / 2 * y 2 at h2
  have hg : gaugeScale / 2 ≠ 0 := div_ne_zero (ne_of_gt gaugeScale_pos) (by norm_num)
  have hn : -gaugeScale / 2 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ne_of_gt gaugeScale_pos)) (by norm_num)
  have hx : x = y := by
    ext i; fin_cases i
    · exact mul_left_cancel₀ hn h0
    · exact mul_left_cancel₀ hg h1
    · exact mul_left_cancel₀ hn h2
  exact congrArg colorStabilizerEquiv hx

def gaugeSlice : Submodule ℝ Gauge := residualOrbit.rangeᗮ

theorem residualOrbit_finrank : Module.finrank ℝ residualOrbit.range = 3 := by
  have h := residualOrbit.finrank_range_add_finrank_ker
  have hk : residualOrbit.ker = ⊥ := LinearMap.ker_eq_bot.mpr residualOrbit_injective
  rw [hk] at h
  simpa only [finrank_bot, add_zero, stabilizer_finrank] using h

theorem gaugeSlice_finrank : Module.finrank ℝ gaugeSlice = 33 := by
  have h := residualOrbit.range.finrank_add_finrank_orthogonal
  rw [residualOrbit_finrank, SourceQuantumNativeDimensions.gauge_finrank] at h
  change Module.finrank ℝ residualOrbit.rangeᗮ = 33
  omega

abbrev SourceLinearSlice := Coframe × scalarSlice × gaugeSlice

theorem sourceLinearSlice_finrank : Module.finrank ℝ SourceLinearSlice = 100 := by
  rw [Module.finrank_prod, Module.finrank_prod, scalarSlice_finrank, gaugeSlice_finrank]
  simp [Coframe]

end LowEnergy.SourceQuantumResidualGaugeSlice
