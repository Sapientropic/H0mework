import H0mework.Physics.LowEnergy.PacketGaugeNoise.Readback
import H0mework.Physics.LowEnergy.LightInteraction.Selected

/-! Constant and real cosine source fields are actual bounded native P286
profiles. Their modulation acts on the same continuous preparation. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise GaugeGreen
open StageNineP286GaugeConnectionVariation StageNineHolonomicField SU7MotherLieAlgebra
noncomputable section
local instance gaugeModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance gaugeCoordinateFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem constantProfile_mem (gauge : P286GaugeOneForm) :
    MemLp (fun _ : Position => gauge) ⊤ volume :=
  memLp_top_of_bound aestronglyMeasurable_const ‖gauge‖ (Filter.Eventually.of_forall fun _ => le_rfl)

def constantProfile (gauge : P286GaugeOneForm) : GaugeProfile :=
  (constantProfile_mem gauge).toLp (fun _ => gauge)

theorem constantProfile_ae (gauge : P286GaugeOneForm) :
    constantProfile gauge=ᵐ[volume] fun _ => gauge :=
  (constantProfile_mem gauge).coeFn_toLp

def selectedProfile : GaugeProfile := constantProfile LightInteraction.sourceGaugeOneForm

theorem constantPotential_ae (gauge : P286GaugeOneForm) (field : FullMatterL2) :
    gaugePotential (constantProfile gauge) field=ᵐ[volume] fun x => gaugeMap gauge (field x) := by
  filter_upwards [gaugePotential_ae (constantProfile gauge) field,constantProfile_ae gauge] with x applied source
  rw [applied,source]

theorem gaugePotential_phase (gauge : GaugeProfile) (shift : Position) (field : FullMatterL2) :
    gaugePotential gauge (phaseShift shift field)=phaseShift shift (gaugePotential gauge field) := by
  apply Lp.ext
  filter_upwards [gaugePotential_ae gauge (phaseShift shift field),phaseShift_position shift field,
    phaseShift_position shift (gaugePotential gauge field),gaugePotential_ae gauge field]
    with x applied modulated outside inside
  rw [applied,modulated,outside,inside,map_smul]

theorem cosineProfile_mem (gauge : P286GaugeOneForm) (probe : Position) :
    MemLp (fun x : Position => Real.cos (2*Real.pi*inner ℝ probe x) • gauge) ⊤ volume := by
  have continuous : Continuous (fun x : Position => Real.cos (2*Real.pi*inner ℝ probe x) • gauge) := by fun_prop
  apply memLp_top_of_bound continuous.aestronglyMeasurable ‖gauge‖
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg gauge)).trans_eq (one_mul _)

def cosineProfile (gauge : P286GaugeOneForm) (probe : Position) : GaugeProfile :=
  (cosineProfile_mem gauge probe).toLp (fun x => Real.cos (2*Real.pi*inner ℝ probe x) • gauge)

theorem cosineProfile_ae (gauge : P286GaugeOneForm) (probe : Position) :
    cosineProfile gauge probe=ᵐ[volume] fun x => Real.cos (2*Real.pi*inner ℝ probe x) • gauge :=
  (cosineProfile_mem gauge probe).coeFn_toLp

theorem cosinePotential (gauge : P286GaugeOneForm) (probe : Position) (field : FullMatterL2) :
    gaugePotential (cosineProfile gauge probe) field=
      cosineShift probe (gaugePotential (constantProfile gauge) field) := by
  apply Lp.ext
  filter_upwards [gaugePotential_ae (cosineProfile gauge probe) field,cosineProfile_ae gauge probe,
    cosineShift_position probe (gaugePotential (constantProfile gauge) field),constantPotential_ae gauge field]
    with x applied source modulated constant
  rw [applied,source,map_smul,modulated,constant]
  simp only [smul_apply,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
