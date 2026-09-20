import H0mework.Physics.QuantumCompatibility.Current
import H0mework.Physics.Dirac.DiracExteriorMatterLocalGaugeLink
import H0mework.Realization.Fields.FirstOrderRemainder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The accepted P286 connection generates a full seven-dimensional smooth
unitary transporter. The Stage 8 link is its first jet with an explicit
source-sized quadratic remainder. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open DiracExteriorMatterLocalGaugeLink
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

abbrev FundamentalMatrix := Matrix SU7MotherIndex SU7MotherIndex ℂ

local instance : NormedAlgebra ℚ FundamentalMatrix := NormedAlgebra.restrictScalars ℚ ℂ _

def actualPotential (point : BasePoint) (direction : LorentzianIndex) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (actual.gaugeConnection point direction)

def connectionGenerator (point : BasePoint) (direction : LorentzianIndex) : FundamentalMatrix :=
  actualPotential point direction

theorem connectionGenerator_star (point : BasePoint) (direction : LorentzianIndex) :
    star (connectionGenerator point direction) = -connectionGenerator point direction :=
  specialUnitaryLieMatrix_star _

def connectionTransport (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    FundamentalMatrix := NormedSpace.exp (duration • connectionGenerator point direction)

theorem connectionTransport_unitary (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    connectionTransport point direction duration ∈ Matrix.unitaryGroup SU7MotherIndex ℂ := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (duration • connectionGenerator point direction) = -(duration • connectionGenerator point direction)
  simp only [star_smul, star_trivial, connectionGenerator_star, smul_neg]

theorem connectionTransport_zero (point : BasePoint) (direction : LorentzianIndex) :
    connectionTransport point direction 0 = 1 := by
  simp [connectionTransport]

theorem connectionTransport_hasDerivAt (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    HasDerivAt (connectionTransport point direction)
      (connectionTransport point direction duration * connectionGenerator point direction) duration :=
  hasDerivAt_exp_smul_const _ _

theorem connectionTransport_firstJet (point : BasePoint) (direction : LorentzianIndex) :
    HasDerivAt (connectionTransport point direction) (connectionGenerator point direction) 0 := by
  simpa only [connectionTransport_zero, Matrix.one_mul] using
    connectionTransport_hasDerivAt point direction 0

def connectionJet (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    FundamentalMatrix := motherFundamentalLinkOfPotential (duration • actualPotential point direction)

theorem connectionJet_eq (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    connectionJet point direction duration = 1 + duration • connectionGenerator point direction := rfl

theorem connectionTransport_remainder (point : BasePoint) (direction : LorentzianIndex)
    (duration : ℝ) (nonnegative : 0 ≤ duration) :
    ‖connectionTransport point direction duration - connectionJet point direction duration‖ ≤
      ‖connectionGenerator point direction‖ ^ 2 * duration ^ 2 := by
  let generator := connectionGenerator point direction
  let velocity (time : ℝ) := connectionTransport point direction time * generator
  let acceleration (time : ℝ) := connectionTransport point direction time * generator ^ 2
  have first (time : ℝ) : HasDerivAt (connectionTransport point direction) (velocity time) time :=
    connectionTransport_hasDerivAt point direction time
  have second (time : ℝ) : HasDerivAt velocity (acceleration time) time := by
    simpa only [velocity, acceleration, pow_two, Matrix.mul_assoc] using (first time).mul_const generator
  have bound (time : ℝ) : ‖acceleration time‖ ≤ ‖generator‖ ^ 2 := by
    dsimp only [acceleration]
    rw [CStarRing.norm_mem_unitary_mul _ (connectionTransport_unitary point direction time)]
    simpa only [pow_two] using norm_mul_le generator generator
  have estimate :=
    NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.FiniteRemainder.firstOrder_error_le
      (connectionTransport point direction) velocity acceleration duration (‖generator‖ ^ 2)
      nonnegative (sq_nonneg _) first second (fun time _ => bound time)
  simpa only [velocity, connectionTransport_zero, Matrix.one_mul, connectionJet_eq,
    sub_add_eq_sub_sub] using estimate

theorem connectionJet_stageEight (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ) :
    exteriorSpinorLinkAction (connectionJet point direction duration) =
      SU7ExteriorMatterGaugeCovariantJet.exteriorSpinorMotherTransport
        (duration • actualPotential point direction) :=
  exteriorSpinorLinkAction_of_motherPotential _

theorem connectionTransport_fullGauge_covariant
    (point : BasePoint) (direction : LorentzianIndex) (duration : ℝ)
    (sourceGauge targetGauge : SU7MotherGroup) :
    (diracExteriorLinkAction (gaugeTransformFundamentalLink sourceGauge targetGauge
      (connectionTransport point direction duration))).comp
        (DiracExteriorMatterAction.diracExteriorMatterGaugeRepresentation targetGauge) =
      (DiracExteriorMatterAction.diracExteriorMatterGaugeRepresentation sourceGauge).comp
        (diracExteriorLinkAction (connectionTransport point direction duration)) :=
  diracExteriorLinkAction_localGauge_covariant _ _ _

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
