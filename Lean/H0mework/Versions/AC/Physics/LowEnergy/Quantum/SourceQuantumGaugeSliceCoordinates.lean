import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceQuantumResidualGaugeSlice
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Two sections of the same actual residual orbit, with generated inverses.
The coordinate section fixes the original gauge rows 0, 6 and 18; its
orthogonal representative uses the original native inner product.
-/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumNativeDimensions SourceQuantumScalarOrbitDimensions SourceQuantumResidualGaugeSlice
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

/-- The three Python gauge-fixing coordinates, in the already proved row order 18,6,0. -/
def coordinateSlice : Submodule ℝ Gauge := orbitRows.ker

theorem coordinateSlice_mem_iff (v : Gauge) : v ∈ coordinateSlice ↔
    (nativeCoordinates (gaugeCoordinates v 0)).1 0 = 0 ∧
    (nativeCoordinates (gaugeCoordinates v 0)).1 6 = 0 ∧
    (nativeCoordinates (gaugeCoordinates v 1)).1 6 = 0 := by
  change orbitRows v = 0 ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    exact ⟨h2, h1, h0⟩
  · rintro ⟨h0,h1,h2⟩
    ext i; fin_cases i
    · exact h2
    · exact h1
    · exact h0

theorem sourceGauge_mem_coordinateSlice : SourceQuantumConfigurationHilbert.sourceGauge ∈ coordinateSlice := by
  change SourceQuantumResidualGaugeSlice.sourceGauge ∈ coordinateSlice
  rw [coordinateSlice_mem_iff]
  simp [sourceGauge_apply, map_smul, colorGenerator_coordinates]

def rowOrbit : stabilizer →ₗ[ℝ] (Fin 3 → ℝ) := orbitRows.comp residualOrbit

private theorem rowOrbit_injective : Function.Injective rowOrbit := by
  intro a b h
  obtain ⟨x, rfl⟩ := colorStabilizerEquiv.surjective a
  obtain ⟨y, rfl⟩ := colorStabilizerEquiv.surjective b
  change orbitRows (residualOrbit (colorStabilizer x)) =
    orbitRows (residualOrbit (colorStabilizer y)) at h
  rw [residualOrbit_minor_action, residualOrbit_minor_action] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change -gaugeScale / 2 * x 0 = -gaugeScale / 2 * y 0 at h0
  change gaugeScale / 2 * x 1 = gaugeScale / 2 * y 1 at h1
  change -gaugeScale / 2 * x 2 = -gaugeScale / 2 * y 2 at h2
  have hp : gaugeScale / 2 ≠ 0 := div_ne_zero (ne_of_gt gaugeScale_pos) (by norm_num)
  have hn : -gaugeScale / 2 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (ne_of_gt gaugeScale_pos)) (by norm_num)
  have hxy : x = y := by
    ext i; fin_cases i
    · exact mul_left_cancel₀ hn h0
    · exact mul_left_cancel₀ hp h1
    · exact mul_left_cancel₀ hn h2
  exact congrArg colorStabilizerEquiv hxy

def rowOrbitEquiv : stabilizer ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  rowOrbit.linearEquivOfInjective rowOrbit_injective (by rw [stabilizer_finrank]; simp)

/-- The actual inverse source minor removes exactly the residual orbit component. -/
def coordinateProjection : Gauge →ₗ[ℝ] Gauge :=
  LinearMap.id - residualOrbit.comp (rowOrbitEquiv.symm.toLinearMap.comp orbitRows)

theorem coordinateProjection_apply (v : Gauge) : coordinateProjection v =
    v - residualOrbit (rowOrbitEquiv.symm (orbitRows v)) := rfl

theorem coordinateProjection_rows (v : Gauge) : orbitRows (coordinateProjection v) = 0 := by
  rw [coordinateProjection_apply, map_sub]
  change orbitRows v - rowOrbitEquiv (rowOrbitEquiv.symm (orbitRows v)) = 0
  rw [rowOrbitEquiv.apply_symm_apply, sub_self]

theorem coordinateProjection_orbit (a : stabilizer) : coordinateProjection (residualOrbit a) = 0 := by
  rw [coordinateProjection_apply]
  change residualOrbit a - residualOrbit (rowOrbitEquiv.symm (rowOrbitEquiv a)) = 0
  rw [rowOrbitEquiv.symm_apply_apply, sub_self]

theorem coordinateProjection_self (v : coordinateSlice) : coordinateProjection (v : Gauge) = v := by
  rw [coordinateProjection_apply]
  have h : orbitRows (v : Gauge) = 0 := v.property
  simp [h]

def orthogonalProjection : Gauge →ₗ[ℝ] gaugeSlice :=
  gaugeSlice.orthogonalProjectionOnto.toLinearMap

theorem orthogonalProjection_orbit (a : stabilizer) :
    orthogonalProjection (residualOrbit a) = 0 := by
  apply (Submodule.orthogonalProjectionOnto_eq_zero_iff).2
  change residualOrbit a ∈ residualOrbit.rangeᗮᗮ
  exact residualOrbit.range.le_orthogonal_orthogonal ⟨a, rfl⟩

theorem orthogonalProjection_self (u : gaugeSlice) : orthogonalProjection (u : Gauge) = u :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u

theorem orthogonal_coordinateProjection (v : Gauge) :
    orthogonalProjection (coordinateProjection v) = orthogonalProjection v := by
  rw [coordinateProjection_apply, map_sub, orthogonalProjection_orbit, sub_zero]

theorem source_difference_in_orbit (v : Gauge) :
    v - (orthogonalProjection v : Gauge) ∈ residualOrbit.range := by
  have h := gaugeSlice.sub_starProjection_mem_orthogonal v
  change v - (orthogonalProjection v : Gauge) ∈ residualOrbit.rangeᗮᗮ at h
  simpa only [Submodule.orthogonal_orthogonal] using h

theorem coordinate_orthogonalProjection (v : Gauge) :
    coordinateProjection (orthogonalProjection v : Gauge) = coordinateProjection v := by
  obtain ⟨a, ha⟩ := source_difference_in_orbit v
  have h : coordinateProjection (v - (orthogonalProjection v : Gauge)) = 0 := by
    rw [← ha, coordinateProjection_orbit]
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Both sections select the same quotient vector by the same source orbit. -/
def sliceEquiv : coordinateSlice ≃ₗ[ℝ] gaugeSlice where
  toFun v := orthogonalProjection v
  invFun u := ⟨coordinateProjection u, coordinateProjection_rows u⟩
  left_inv v := by
    apply Subtype.ext
    exact (coordinate_orthogonalProjection v).trans (coordinateProjection_self v)
  right_inv u := by
    exact (orthogonal_coordinateProjection u).trans (orthogonalProjection_self u)
  map_add' := by intros; exact map_add orthogonalProjection _ _
  map_smul' := by intros; exact map_smul orthogonalProjection _ _

theorem sliceEquiv_apply (v : coordinateSlice) : sliceEquiv v = orthogonalProjection v := rfl

theorem sliceEquiv_symm_apply (u : gaugeSlice) :
    (sliceEquiv.symm u : Gauge) = coordinateProjection u := rfl

/-- The full source tangent orbit chart and its explicit inverse minor. -/
def sourceSplitEquiv : (stabilizer × coordinateSlice) ≃ₗ[ℝ] Gauge where
  toFun av := residualOrbit av.1 + av.2
  invFun v := (rowOrbitEquiv.symm (orbitRows v),
    ⟨coordinateProjection v, coordinateProjection_rows v⟩)
  left_inv av := by
    apply Prod.ext
    · change rowOrbitEquiv.symm (orbitRows (residualOrbit av.1 + (av.2 : Gauge))) = av.1
      rw [map_add]
      have h : orbitRows (av.2 : Gauge) = 0 := av.2.property
      rw [h, add_zero]
      exact rowOrbitEquiv.symm_apply_apply av.1
    · apply Subtype.ext
      change coordinateProjection (residualOrbit av.1 + (av.2 : Gauge)) = av.2
      rw [map_add, coordinateProjection_orbit, zero_add, coordinateProjection_self]
  right_inv v := by
    change residualOrbit (rowOrbitEquiv.symm (orbitRows v)) + coordinateProjection v = v
    rw [coordinateProjection_apply]
    abel
  map_add' := by intros; simp [map_add]; abel
  map_smul' := by intros; simp [map_smul, smul_add]

abbrev SourceCoordinateSlice := Coframe × scalarSlice × coordinateSlice

def commonSliceEquiv : SourceCoordinateSlice ≃ₗ[ℝ] SourceLinearSlice :=
  (LinearEquiv.refl ℝ Coframe).prodCongr ((LinearEquiv.refl ℝ scalarSlice).prodCongr sliceEquiv)

end LowEnergy.SourceQuantumGaugeSliceCoordinates
