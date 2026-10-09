import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

theorem gain_positive (current : Material) (valid : Admissible current) : 0 < gainQ current :=
  div_pos valid.positiveReserve (by nlinarith [valid.positiveKinetic,valid.positiveReserve])

theorem gain_lt_one (current : Material) (valid : Admissible current) : gainQ current < 1 := by
  unfold gainQ
  apply (div_lt_one (by nlinarith [valid.positiveKinetic,valid.positiveReserve])).2
  nlinarith [valid.positiveKinetic,valid.positiveReserve]

theorem gain_balance (current : Material) (valid : Admissible current) :
    gainQ current*(8*(current.body.frame.kinetic+current.reserve+1))=current.reserve := by
  unfold gainQ
  exact div_mul_cancel₀ _ (ne_of_gt (by nlinarith [valid.positiveKinetic,valid.positiveReserve]))

theorem positive_debit_below_reserve (current : Material) (valid : Admissible current) :
    0 < nextKineticQ current-current.body.frame.kinetic ∧
      nextKineticQ current-current.body.frame.kinetic < current.reserve/2 := by
  have gp := gain_positive current valid
  have g1 := gain_lt_one current valid
  have kp := valid.positiveKinetic
  have rp := valid.positiveReserve
  have g2 : (gainQ current)^2 ≤ gainQ current := by nlinarith
  have g2k := mul_le_mul_of_nonneg_right g2 kp.le
  have small : 8*gainQ current*current.body.frame.kinetic < current.reserve := by
    have other : 0 < gainQ current*(current.reserve+1) := mul_pos gp (by linarith)
    nlinarith [gain_balance current valid]
  unfold nextKineticQ
  constructor
  · have growth : 0 < ((1+gainQ current)^2-1)*current.body.frame.kinetic :=
      mul_pos (by nlinarith) kp
    nlinarith
  · calc
      (1+gainQ current)^2*current.body.frame.kinetic-current.body.frame.kinetic ≤
          3*gainQ current*current.body.frame.kinetic := by nlinarith
      _ < current.reserve/2 := by linarith

theorem stock_positive (current : Material) (valid : Admissible current) :
    0 < current.body.resource.momentum :=
  (Rat.cast_pos.mpr valid.positiveReserve).trans valid.reserveBelowStock

theorem next_stock (current : Material) (valid : Admissible current) :
    current.body.resource.momentum/2 < (nextMaterial current).body.resource.momentum := by
  have debit : (nextKineticQ current : ℝ)-(current.body.frame.kinetic : ℝ)<(current.reserve : ℝ)/2 := by
    exact_mod_cast (positive_debit_below_reserve current valid).2
  change current.body.resource.momentum/2<current.body.resource.momentum+
    (current.body.frame.kinetic : ℝ)-(nextKineticQ current : ℝ)
  linarith only [debit,valid.reserveBelowStock]

theorem next_reserve (current : Material) (valid : Admissible current) :
    0 < (nextMaterial current).reserve ∧
    ((nextMaterial current).reserve : ℝ)<(nextMaterial current).body.resource.momentum := by
  constructor
  · exact half_pos valid.positiveReserve
  · change ((current.reserve/2 : ℚ) : ℝ)<(nextMaterial current).body.resource.momentum
    push_cast
    linarith only [valid.reserveBelowStock,next_stock current valid]

theorem next_momentum (current : Material) (i : Coordinate) :
    momentum (nextMaterial current) i=(1+(gainQ current : ℝ))*momentum current i := by
  simp [momentum,nextMaterial,nextFrame]

theorem next_kinetic_generated (current : Material) (valid : Admissible current) :
    nuclearKinetic (momentum (nextMaterial current))=((nextMaterial current).body.frame.kinetic : ℝ) := by
  have same : momentum (nextMaterial current)=fun i => (1+(gainQ current : ℝ))*momentum current i :=
    funext (next_momentum current)
  rw [same,FiniteActuation.kinetic_scale,valid.kinetic]
  change (1+(gainQ current : ℝ))^2*(current.body.frame.kinetic : ℝ)=(nextKineticQ current : ℝ)
  simp [nextKineticQ]

theorem next_admissible (current : Material) (valid : Admissible current) : Admissible (nextMaterial current) :=
  { positiveReserve := (next_reserve current valid).1
    reserveBelowStock := (next_reserve current valid).2
    positiveKinetic := by
      change 0 < nextKineticQ current
      linarith only [(positive_debit_below_reserve current valid).1,valid.positiveKinetic]
    kinetic := next_kinetic_generated current valid
    total := rfl
    position := valid.position
    force := valid.force
    potential := valid.potential
    held := valid.held
    realized := valid.realized
    inheritedResidual := valid.inheritedResidual
    newNumericalResidual := valid.newNumericalResidual }

theorem next_mechanical_account (current : Material) (valid : Admissible current) :
    Extract.Port.kinetic (nextMaterial current).body.resource.momentum+
      ((nextMaterial current).body.frame.total : ℝ)=
    Extract.Port.kinetic current.body.resource.momentum+(current.body.frame.total : ℝ) := by
  have positive := stock_positive current valid
  have nextPositive := (half_pos positive).trans (next_stock current valid)
  rw [Extract.Port.kinetic,Extract.Port.kinetic,abs_of_pos nextPositive,abs_of_pos positive,valid.total]
  change current.body.resource.momentum+(current.body.frame.kinetic : ℝ)-(nextKineticQ current : ℝ)+
    ((nextKineticQ current+current.body.frame.potential : ℚ) : ℝ)=_
  push_cast
  ring

theorem next_whole_account (current : Material) (valid : Admissible current) :
    Live.freeEnergy (nextMaterial current).body.resource.quantum+Live.entropyProduction (nextMaterial current).body.resource.quantum+
      Extract.Port.kinetic (nextMaterial current).body.resource.momentum+((nextMaterial current).body.frame.total : ℝ)=
    Live.freeEnergy current.body.resource.quantum+Live.entropyProduction current.body.resource.quantum+
      Extract.Port.kinetic current.body.resource.momentum+(current.body.frame.total : ℝ) := by
  have a := Live.loadNext_net_account current.body.resource.quantum
  have b := Live.loadNext_net_account (Live.loadNext current.body.resource.quantum)
  have c := Live.loadNext_net_account (Live.loadNext (Live.loadNext current.body.resource.quantum))
  have body := next_mechanical_account current valid
  change Live.freeEnergy (Live.loadNext (Live.loadNext (Live.loadNext current.body.resource.quantum)))+
    Live.entropyProduction (Live.loadNext (Live.loadNext (Live.loadNext current.body.resource.quantum)))+_+_=_
  linarith only [a,b,c,body]

theorem next_clocks (current : Material) :
    (nextMaterial current).body.resource.quantum.localClock=current.body.resource.quantum.localClock+3*Propagation.Producer.nativeClockStep ∧
    (nextMaterial current).body.bodyClock=current.body.bodyClock+3*Propagation.Producer.nativeClockStep := by
  constructor
  · change (Live.loadNext (Live.loadNext (Live.loadNext current.body.resource.quantum))).localClock=_
    rw [Live.loadNext_clock,Live.loadNext_clock,Live.loadNext_clock]
    ring
  · rfl

theorem next_changes_momentum (current : Material) (valid : Admissible current) :
    (nextMaterial current).body.frame.momentum ≠ current.body.frame.momentum := by
  intro same
  have vector : momentum (nextMaterial current)=momentum current := by
    funext i
    exact congrArg (fun p => (p i.1 i.2 : ℝ)) same
  have exactK := next_kinetic_generated current valid
  rw [vector,valid.kinetic] at exactK
  have rational : current.body.frame.kinetic=nextKineticQ current := Rat.cast_injective exactK
  have positive := (positive_debit_below_reserve current valid).1
  rw [← rational,sub_self] at positive
  exact (lt_irrefl 0) positive

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
