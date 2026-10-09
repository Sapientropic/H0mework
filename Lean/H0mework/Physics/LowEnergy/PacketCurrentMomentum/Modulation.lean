import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Density

/-! A physical outgoing phase acts on the external field position, whose
values are still entire matter-state vectors. This is a genuine bounded map. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem phaseValue_memLp (shift : Position) (field : FieldSpace E) :
    MemLp (fun position : Position => positionPhase shift position • field position) 2 volume := by
  apply (Lp.memLp field).of_le
    ((positionPhase_continuous shift).aestronglyMeasurable.smul (Lp.memLp field).aestronglyMeasurable)
  filter_upwards with position
  change ‖positionPhase shift position • field position‖≤‖field position‖
  rw [norm_smul,positionPhase_norm,one_mul]

def phaseValue (shift : Position) (field : FieldSpace E) : FieldSpace E := (phaseValue_memLp shift field).toLp _

theorem phaseValue_ae (shift : Position) (field : FieldSpace E) :
    phaseValue shift field=ᵐ[volume] fun position => positionPhase shift position • field position :=
  (phaseValue_memLp shift field).coeFn_toLp

theorem phaseValue_add (shift : Position) (first second : FieldSpace E) :
    phaseValue shift (first+second)=phaseValue shift first+phaseValue shift second := by
  apply Lp.ext
  filter_upwards [phaseValue_ae shift (first+second),phaseValue_ae shift first,phaseValue_ae shift second,
    Lp.coeFn_add first second,Lp.coeFn_add (phaseValue shift first) (phaseValue shift second)]
    with position whole left right input output
  simp only [whole,output,input,Pi.add_apply,left,right,smul_add]

theorem phaseValue_smul (shift : Position) (scalar : ℂ) (field : FieldSpace E) :
    phaseValue shift (scalar • field)=scalar • phaseValue shift field := by
  apply Lp.ext
  filter_upwards [phaseValue_ae shift (scalar • field),phaseValue_ae shift field,
    Lp.coeFn_smul scalar field,Lp.coeFn_smul scalar (phaseValue shift field)] with position whole inside input output
  simp only [whole,output,input,Pi.smul_apply,inside,smul_smul,mul_comm]

theorem phaseValue_bound (shift : Position) (field : FieldSpace E) : ‖phaseValue shift field‖≤‖field‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [phaseValue_ae shift field] with position value
  rw [value,norm_smul,positionPhase_norm,one_mul]

def phaseLinear (shift : Position) : FieldSpace E →ₗ[ℂ] FieldSpace E where
  toFun := phaseValue shift
  map_add' := phaseValue_add shift
  map_smul' := phaseValue_smul shift

def phaseMap (shift : Position) : FieldSpace E →L[ℂ] FieldSpace E :=
  (phaseLinear shift).mkContinuous 1 (fun field => by
    change ‖phaseValue shift field‖≤1*‖field‖
    simpa only [one_mul] using phaseValue_bound shift field)

theorem phaseMap_ae (shift : Position) (field : FieldSpace E) :
    phaseMap shift field=ᵐ[volume] fun position => positionPhase shift position • field position := phaseValue_ae shift field

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
