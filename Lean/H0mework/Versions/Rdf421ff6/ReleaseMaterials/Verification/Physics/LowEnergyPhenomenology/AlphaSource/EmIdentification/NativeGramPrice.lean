import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.TensorPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualNativePreparedLegPriceOwn
open SaturationMonoid.PhysicsCore
open StageNineDynamicBreakingVacuum SU7ExteriorMatterRestriction
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open CanonicalPreparationCutoff PreparationScalarCoordinates PreparationChartGuard
open GaussComposite.SourceGraph ActualSourceFiniteYukawaPriceOwn GaussNativePotential
open scoped BigOperators

local instance : DecidableEq ScalarBasisIndex := Classical.decEq _

theorem original_scalar_coordinate_read (phi : Scalar) (a : ScalarBasisIndex) :
    (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm phi) a = phi a := by
  have h := congrArg (fun x : Scalar => x a) (scalarCoordinateEquiv.apply_symm_apply phi)
  exact h

theorem original_composite_coefficient_bound (channel : Fin 2) (color : Fin 3)
    (z : SourceCoordinateSlice) : ‖GaussComposite.coefficient channel color z‖ ≤ ‖scalarField z‖ := by
  change ‖(if color = 1 then (-1 : ℂ) else 1) *
    (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm (scalarField z))
      (LowEnergy.Electromagnetic.Identification.Composite.scalarBasis channel color)‖ ≤ _
  rw [original_scalar_coordinate_read, norm_mul]
  have sign : ‖(if color = 1 then (-1 : ℂ) else 1)‖ = 1 := by
    split_ifs <;> norm_num
  rw [sign, one_mul]
  exact PiLp.norm_apply_le (scalarField z) _

theorem original_native_scalar_box_norm (z : SourceCoordinateSlice)
    (inside : z ∈ tsupport actualNativeLocalizer) : ‖(z.2.1 : Scalar)‖ ≤ 16 * sourceRadius := by
  change z ∈ tsupport nativePsi at inside
  have h := scalar_box_norm (fullCoordinates z) (nativePsi_tsupport inside)
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

theorem original_native_scalarField_bound (z : SourceCoordinateSlice)
    (inside : z ∈ tsupport actualNativeLocalizer) : ‖scalarField z‖ ≤ 5 := by
  have h := original_native_scalar_box_norm z inside
  have triangle := norm_add_le SourceQuantumScalarChart.vacuum (z.2.1 : Scalar)
  change ‖SourceQuantumScalarChart.vacuum + (z.2.1 : Scalar)‖ ≤ 5
  nlinarith [original_vacuum_norm_bound, radius_small.2]

theorem original_native_gramWeight_bound (z : SourceCoordinateSlice)
    (inside : z ∈ tsupport actualNativeLocalizer) : gramWeight z ≤ 151 := by
  have each (channel : Fin 2) (color : Fin 3) :
      ‖GaussComposite.coefficient channel color z‖ ^ 2 ≤ 25 := by
    have h := (original_composite_coefficient_bound channel color z).trans
      (original_native_scalarField_bound z inside)
    nlinarith [norm_nonneg (GaussComposite.coefficient channel color z)]
  unfold gramWeight
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (a : Fin 2) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (c : Fin 3) _ => each a c))
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  linarith

theorem original_native_sqrt_gramWeight_bound (z : SourceCoordinateSlice)
    (inside : z ∈ tsupport actualNativeLocalizer) : Real.sqrt (gramWeight z) ≤ 13 := by
  have squared := Real.sq_sqrt (gramWeight_pos z).le
  nlinarith [original_native_gramWeight_bound z inside, Real.sqrt_nonneg (gramWeight z)]

end LowEnergy.ActualNativePreparedLegPriceOwn
