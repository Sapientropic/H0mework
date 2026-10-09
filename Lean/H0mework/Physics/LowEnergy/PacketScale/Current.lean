import H0mework.Physics.LowEnergy.PacketScale.Cutoff
import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Overlap

/-! At nonzero outgoing momentum, a finite scale update retains its shell-shell
term and both low-shell orders. Zero-momentum cancellation is proved from the
same spectral supports rather than assumed for different source transfers. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Classical
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
open FullQuantum FullSpace PacketField PacketNoise PacketCurrentMomentum
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def mixedCurrent (current : Matrix ι ι ℝ) (left right : ι → FieldSpace E) (momentum : Position) : ℂ :=
  (1/4 : ℂ)*∑ first, ∑ second, (current first second : ℂ)*
    (inner ℂ (left first) (translation (physicalTransfer momentum) (right second))+
      inner ℂ (left second) (translation (physicalTransfer momentum) (right first)))

omit [CompleteSpace E] in
theorem cutoff_shifted_pair (leftRadius rightRadius : ℝ) (left right : FieldSpace E) (momentum : Position) :
    inner ℂ (cutoff leftRadius left) (translation (physicalTransfer momentum) (cutoff rightRadius right))=
      ∫ frequency : Position,
        if frequency∈scaleSet leftRadius ∧ frequency-physicalTransfer momentum∈scaleSet rightRadius then
          inner ℂ (left frequency) (right (frequency-physicalTransfer momentum)) else 0 := by
  classical
  rw [L2.inner_def]
  have moved := (measurePreserving_sub_right volume (physicalTransfer momentum)).quasiMeasurePreserving.ae
    (cutoff_ae rightRadius right)
  apply integral_congr_ae
  filter_upwards [cutoff_ae leftRadius left,moved,
    translation_ae (physicalTransfer momentum) (cutoff rightRadius right)] with frequency first second translated
  rw [first,translated,second]
  by_cases inLeft : frequency∈scaleSet leftRadius <;>
    by_cases inRight : frequency-physicalTransfer momentum∈scaleSet rightRadius <;> simp [inLeft,inRight]

theorem mixedCurrent_diagonal (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (momentum : Position) :
    mixedCurrent current field field momentum=outgoing current (fun row => spatialFourier (field row)) momentum :=
  (outgoing_spectrum current field momentum).symm

omit [CompleteSpace E] in
theorem mixedCurrent_add_left (current : Matrix ι ι ℝ) (left middle right : ι → FieldSpace E) (momentum : Position) :
    mixedCurrent current (left+middle) right momentum=
      mixedCurrent current left right momentum+mixedCurrent current middle right momentum := by
  simp only [mixedCurrent,Pi.add_apply,inner_add_left]
  simp only [← Finset.sum_add_distrib,← mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

omit [CompleteSpace E] in
theorem mixedCurrent_add_right (current : Matrix ι ι ℝ) (left middle right : ι → FieldSpace E) (momentum : Position) :
    mixedCurrent current left (middle+right) momentum=
      mixedCurrent current left middle momentum+mixedCurrent current left right momentum := by
  simp only [mixedCurrent,Pi.add_apply,map_add,inner_add_right]
  simp only [← Finset.sum_add_distrib,← mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

omit [CompleteSpace E] in
theorem translation_zero (field : FieldSpace E) : translation 0 field=field := by
  apply Lp.ext
  filter_upwards [translation_ae 0 field] with frequency value
  simpa only [sub_zero] using value

theorem scale_current_difference (current : Matrix ι ι ℝ) (field : ι → FieldSpace E)
    (innerRadius outerRadius : ℝ) (momentum : Position) :
    outgoing current (fun row => spatialFourier (cutoff outerRadius (field row))) momentum-
      outgoing current (fun row => spatialFourier (cutoff innerRadius (field row))) momentum=
    outgoing current (fun row => spatialFourier (shell innerRadius outerRadius (field row))) momentum+
      mixedCurrent current (fun row => cutoff innerRadius (field row)) (fun row => shell innerRadius outerRadius (field row)) momentum+
      mixedCurrent current (fun row => shell innerRadius outerRadius (field row)) (fun row => cutoff innerRadius (field row)) momentum := by
  simp_rw [← mixedCurrent_diagonal]
  have decomposition : (fun row => cutoff outerRadius (field row))=
      (fun row => cutoff innerRadius (field row))+(fun row => shell innerRadius outerRadius (field row)) := by
    funext row
    exact shell_decomposition innerRadius outerRadius (field row)
  rw [decomposition,mixedCurrent_add_left,mixedCurrent_add_right,mixedCurrent_add_right]
  ring

omit [CompleteSpace E] in
theorem mixed_low_shell_zero (current : Matrix ι ι ℝ) (field : ι → FieldSpace E)
    (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius) :
    mixedCurrent current (fun row => cutoff innerRadius (field row)) (fun row => shell innerRadius outerRadius (field row)) 0=0 := by
  simp only [mixedCurrent,physicalTransfer,smul_zero,translation_zero,
    shell_low_orthogonal innerRadius outerRadius ordered,add_zero,mul_zero,Finset.sum_const_zero]

omit [CompleteSpace E] in
theorem mixed_shell_low_zero (current : Matrix ι ι ℝ) (field : ι → FieldSpace E)
    (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius) :
    mixedCurrent current (fun row => shell innerRadius outerRadius (field row)) (fun row => cutoff innerRadius (field row)) 0=0 := by
  simp only [mixedCurrent,physicalTransfer,smul_zero,translation_zero,
    low_shell_orthogonal innerRadius outerRadius ordered,add_zero,mul_zero,Finset.sum_const_zero]

theorem scale_current_difference_zero (current : Matrix ι ι ℝ) (field : ι → FieldSpace E)
    (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius) :
    outgoing current (fun row => spatialFourier (cutoff outerRadius (field row))) 0-
      outgoing current (fun row => spatialFourier (cutoff innerRadius (field row))) 0=
    outgoing current (fun row => spatialFourier (shell innerRadius outerRadius (field row))) 0 := by
  rw [scale_current_difference,mixed_low_shell_zero current field innerRadius outerRadius ordered,
    mixed_shell_low_zero current field innerRadius outerRadius ordered,add_zero,add_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
