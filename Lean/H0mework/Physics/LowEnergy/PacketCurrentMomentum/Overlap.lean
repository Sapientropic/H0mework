import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Outgoing
import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Pairing

/-! The nonzero outgoing current is the full two-order translated spectrum
overlap, with one Taylor half and no assumption of momentum orthogonality. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem outgoing_phase (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (momentum : Position) :
    outgoing current field momentum=∫ position : Position,
      positionPhase (-physicalTransfer momentum) position*(density current field position : ℂ) := by
  unfold outgoing
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with position
  have argument : -2*Real.pi*inner ℝ position (physicalTransfer momentum)=
      2*Real.pi*inner ℝ (-physicalTransfer momentum) position := by
    rw [inner_neg_left,real_inner_comm]
    ring
  simp only [positionPhase,argument,smul_eq_mul]

theorem phaseRealPair_integrable (shift : Position) (left right : FieldSpace E) :
    Integrable (fun position : Position => positionPhase shift position*
      ((inner ℂ (left position) (right position)).re : ℂ)) volume := by
  exact ((L2.integrable_inner (𝕜 := ℂ) left right).re.ofReal).bdd_mul
    (positionPhase_continuous shift).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun position => (positionPhase_norm shift position).le))

theorem outgoing_pair (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (momentum : Position) :
    outgoing current field momentum=(1/4 : ℂ)*∑ first, ∑ second, (current first second : ℂ)*
      (inner ℂ (field first) (phaseMap (-physicalTransfer momentum) (field second))+
        inner ℂ (field second) (phaseMap (-physicalTransfer momentum) (field first))) := by
  have term (first second : ι) :=
    (phaseRealPair_integrable (-physicalTransfer momentum) (field first) (field second)).const_mul (current first second : ℂ)
  have expand (position : Position) :
      positionPhase (-physicalTransfer momentum) position*(density current field position : ℂ)=
      (1/2 : ℂ)*∑ first, ∑ second, (current first second : ℂ)*
        (positionPhase (-physicalTransfer momentum) position*
          ((inner ℂ (field first position) (field second position)).re : ℂ)) := by
    simp only [density,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [outgoing_phase]
  simp_rw [expand]
  rw [integral_const_mul,integral_finsetSum _ (fun first _ => integrable_finsetSum _ (fun second _ => term first second))]
  simp_rw [integral_finsetSum _ (fun second _ => term _ second),integral_const_mul,phaseRealPair_integral]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

variable [CompleteSpace E]

theorem outgoing_spectrum (current : Matrix ι ι ℝ) (spectrum : ι → FieldSpace E) (momentum : Position) :
    outgoing current (fun row => spatialFourier (spectrum row)) momentum=
      (1/4 : ℂ)*∑ first, ∑ second, (current first second : ℂ)*
        (inner ℂ (spectrum first) (translation (physicalTransfer momentum) (spectrum second))+
          inner ℂ (spectrum second) (translation (physicalTransfer momentum) (spectrum first))) := by
  rw [outgoing_pair]
  simp_rw [translated_pair]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
