import H0mework.Physics.LowEnergy.PacketField.Spatial
import Mathlib.Topology.ContinuousMap.Compact

/-! The actual physical-band extension with a bounded Borel pole coefficient
is a bounded linear map from continuous band fields into ambient L². -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
open FullQuantum FullSpace PacketPairResponse PacketField
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem physicalBand_inside (field : LightBand → E) (frequency : Position)
    (inside : ‖(2*Real.pi) • frequency‖≤bandRadius) :
    physicalBand field frequency=field ⟨(2*Real.pi) • frequency,inside⟩ :=
  extendBand_inside field ⟨(2*Real.pi) • frequency,inside⟩

omit [NormedSpace ℂ E] in
theorem physicalBand_outside (field : LightBand → E) (frequency : Position)
    (outside : ¬‖(2*Real.pi) • frequency‖≤bandRadius) :
    physicalBand field frequency=0 :=
  extendBand_outside field _ outside

omit [NormedSpace ℂ E] in
theorem physicalBand_add (first second : LightBand → E) :
    physicalBand (fun point => first point+second point)=physicalBand first+physicalBand second := by
  funext frequency
  by_cases inside : ‖(2*Real.pi) • frequency‖≤bandRadius
  · simp only [Pi.add_apply,physicalBand_inside _ _ inside]
  · simp only [Pi.add_apply,physicalBand_outside _ _ inside,add_zero]

theorem physicalBand_smul (scalar : ℂ) (field : LightBand → E) :
    physicalBand (fun point => scalar • field point)=scalar • physicalBand field := by
  funext frequency
  by_cases inside : ‖(2*Real.pi) • frequency‖≤bandRadius
  · simp only [Pi.smul_apply,physicalBand_inside _ _ inside]
  · simp only [Pi.smul_apply,physicalBand_outside _ _ inside,smul_zero]

def unitBand : FieldSpace ℝ :=
  (physicalBand_memLp (fun _ => (1 : ℝ)) stronglyMeasurable_const 1 (by norm_num)
    (fun _ => by norm_num)).toLp _

theorem unitBand_ae : unitBand=ᵐ[volume] physicalBand (fun _ => (1 : ℝ)) :=
  (physicalBand_memLp (fun _ => (1 : ℝ)) stronglyMeasurable_const 1 (by norm_num)
    (fun _ => by norm_num)).coeFn_toLp

variable (weight : LightBand → ℂ) (measurableWeight : StronglyMeasurable weight)
  (bound : ℝ) (nonnegative : 0≤bound) (bounded : ∀ point, ‖weight point‖≤bound)

include measurableWeight nonnegative bounded in
theorem weighted_memLp (field : C(LightBand,E)) :
    MemLp (physicalBand (fun point => weight point • field point)) 2 (volume : Measure Position) := by
  apply physicalBand_memLp _ (measurableWeight.smul field.continuous.stronglyMeasurable)
    (bound*‖field‖) (mul_nonneg nonnegative (norm_nonneg _))
  intro point
  change ‖weight point • field point‖≤bound*‖field‖
  rw [norm_smul]
  exact mul_le_mul (bounded point) (field.norm_coe_le_norm point) (norm_nonneg _) nonnegative

def weightedValue (field : C(LightBand,E)) : FieldSpace E :=
  (weighted_memLp weight measurableWeight bound nonnegative bounded field).toLp _

theorem weightedValue_ae (field : C(LightBand,E)) :
    weightedValue weight measurableWeight bound nonnegative bounded field=ᵐ[volume]
      physicalBand (fun point => weight point • field point) :=
  (weighted_memLp weight measurableWeight bound nonnegative bounded field).coeFn_toLp

def weightedLinear : C(LightBand,E) →ₗ[ℂ] FieldSpace E where
  toFun := weightedValue weight measurableWeight bound nonnegative bounded
  map_add' first second := by
    apply Lp.ext
    filter_upwards [weightedValue_ae weight measurableWeight bound nonnegative bounded (first+second),
      weightedValue_ae weight measurableWeight bound nonnegative bounded first,
      weightedValue_ae weight measurableWeight bound nonnegative bounded second,
      Lp.coeFn_add (weightedValue weight measurableWeight bound nonnegative bounded first)
        (weightedValue weight measurableWeight bound nonnegative bounded second)] with frequency sum left right add
    rw [add,sum]
    simp only [Pi.add_apply]
    rw [left,right]
    simp only [ContinuousMap.add_apply,smul_add,physicalBand_add,Pi.add_apply]
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards [weightedValue_ae weight measurableWeight bound nonnegative bounded (scalar • field),
      weightedValue_ae weight measurableWeight bound nonnegative bounded field,
      Lp.coeFn_smul scalar (weightedValue weight measurableWeight bound nonnegative bounded field)] with frequency scaled original smul
    simp only [RingHom.id_apply]
    rw [smul,scaled]
    simp only [Pi.smul_apply]
    rw [original]
    simp only [ContinuousMap.smul_apply,smul_comm (weight _) scalar,physicalBand_smul,Pi.smul_apply]

theorem weightedValue_bound (field : C(LightBand,E)) :
    ‖weightedValue weight measurableWeight bound nonnegative bounded field‖≤(bound*‖unitBand‖)*‖field‖ := by
  have estimate : ‖weightedValue weight measurableWeight bound nonnegative bounded field‖≤
      (bound*‖field‖)*‖unitBand‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [weightedValue_ae weight measurableWeight bound nonnegative bounded field,unitBand_ae]
      with frequency value unit
    rw [value,unit]
    by_cases inside : ‖(2*Real.pi) • frequency‖≤bandRadius
    · rw [physicalBand_inside _ _ inside,physicalBand_inside _ _ inside,norm_smul]
      simp only [norm_one,mul_one]
      exact mul_le_mul (bounded _) (field.norm_coe_le_norm _) (norm_nonneg _) nonnegative
    · simp only [physicalBand_outside _ _ inside,norm_zero,mul_zero,le_refl]
  exact estimate.trans_eq (by ring)

def weightedLift : C(LightBand,E) →L[ℂ] FieldSpace E :=
  (weightedLinear weight measurableWeight bound nonnegative bounded).mkContinuous
    (bound*‖unitBand‖) (weightedValue_bound weight measurableWeight bound nonnegative bounded)

theorem weightedLift_ae (field : C(LightBand,E)) :
    weightedLift weight measurableWeight bound nonnegative bounded field=ᵐ[volume]
      physicalBand (fun point => weight point • field point) :=
  weightedValue_ae weight measurableWeight bound nonnegative bounded field

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFieldTime
