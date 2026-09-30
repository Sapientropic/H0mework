import H0mework.Physics.LowEnergy.PacketFourier.Counting

/-! Both temporal orderings of the opposite Fourier pair are read on the original source, after same-sign terms cancel between quadratures. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics HistoryPrepared Stage9DEF
noncomputable section

theorem quadrature_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (firstPlus firstMinus secondPlus secondMinus : E) :
    inner ℂ ((1/2 : ℂ) • (firstPlus+firstMinus)) ((1/2 : ℂ) • (secondPlus+secondMinus))+
      inner ℂ ((2*Complex.I)⁻¹ • (firstPlus-firstMinus)) ((2*Complex.I)⁻¹ • (secondPlus-secondMinus))=
      (1/2 : ℂ)*(inner ℂ firstPlus secondPlus+inner ℂ firstMinus secondMinus) := by
  have scale (scalar : ℂ) (left right : E) :
      inner ℂ (scalar • left) (scalar • right)=(Complex.normSq scalar : ℂ)*inner ℂ left right := by
    rw [inner_smul_left,inner_smul_right,← mul_assoc,← Complex.normSq_eq_conj_mul_self]
  rw [scale,scale]
  norm_num [Complex.normSq_mul,Complex.normSq_inv]
  ring

def oppositeCovariance (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (left right : ℝ) : ℂ :=
  (1/2 : ℂ)*(phaseCovariance energy damping positive shift shift left right+
    phaseCovariance energy damping positive (-shift) (-shift) left right)

theorem quadrature_pair (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (left right : ℝ) :
    inner ℂ (packetCurrent energy damping positive shift left) (packetCurrent energy damping positive shift right)+
      inner ℂ (sinePacket energy damping positive shift left) (sinePacket energy damping positive shift right)=
        oppositeCovariance energy damping positive shift left right := by
  rw [packet_cosine,packet_cosine,packet_sine,packet_sine]
  exact quadrature_gram _ _ _ _

def oppositeObservable (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (left right : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (1/2 : ℂ) • (phaseCovarianceObservable energy damping positive shift shift left right+
    phaseCovarianceObservable energy damping positive (-shift) (-shift) left right)

theorem opposite_source_read (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (left right : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (oppositeObservable energy damping positive shift left right)))=
      oppositeCovariance energy damping positive shift left right := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((1/2 : ℂ) •
    ((phaseCenteredFilter energy damping positive shift left).adjoint
        (phaseCenteredFilter energy damping positive shift right preparedPacket)+
      (phaseCenteredFilter energy damping positive (-shift) left).adjoint
        (phaseCenteredFilter energy damping positive (-shift) right preparedPacket)))=_
  rw [inner_smul_right,inner_add_right,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem opposite_source_diagonal (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (oppositeObservable energy damping positive shift time time)))=
      (oppositeNoise energy damping positive shift time : ℂ) := by
  rw [opposite_source_read,oppositeCovariance,phaseNoise_read,phaseNoise_read]
  simp only [oppositeNoise,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
