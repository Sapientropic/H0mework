import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondResponse.Pair
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondResponse.Polynomial

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondResponse
noncomputable section
open CPS1Deformation
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

def relativePosition {source : CPS1ElectronicSource.State frame}
    (positions : NuclearConfiguration source) (site : BridgeSite source) : CPS1ElectronicSource.Point :=
  positions site.phosphate.nuclear-positions site.oxygenNuclear

def relativeVelocity (state : Material frame) (site : BridgeSite state.reference) : CPS1ElectronicSource.Point :=
  fun axis => state.momenta site.phosphate.nuclear axis / CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear -
    state.momenta site.oxygenNuclear axis / CPS1MolecularFrame.inertia state.reference site.oxygenNuclear

def relativeQuadratic (state : Material frame) (site : BridgeSite state.reference) : CPS1ElectronicSource.Point :=
  fun axis => state.jointForce site.phosphate.nuclear axis / (2*CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear) -
    state.jointForce site.oxygenNuclear axis / (2*CPS1MolecularFrame.inertia state.reference site.oxygenNuclear)

def squaredDistance {source : CPS1ElectronicSource.State frame}
    (positions : NuclearConfiguration source) (site : BridgeSite source) : ℝ :=
  ∑ axis : Fin 3, (relativePosition positions site axis)^2

theorem squared_distance_norm {source : CPS1ElectronicSource.State frame}
    (positions : NuclearConfiguration source) (site : BridgeSite source) :
    squaredDistance positions site = ‖CPS1ElectronicSource.euclideanPoint (relativePosition positions site)‖^2 :=
  (EuclideanSpace.real_norm_sq_eq (CPS1ElectronicSource.euclideanPoint (relativePosition positions site))).symm

def distancePolynomial (state : Material frame) (site : BridgeSite state.reference) : Generic.Quartic :=
  let r := relativePosition state.positions site
  let v := relativeVelocity state site
  let a := relativeQuadratic state site
  ⟨∑ axis : Fin 3, 2*r axis*v axis,
   ∑ axis : Fin 3, ((v axis)^2+2*r axis*a axis),
   ∑ axis : Fin 3, 2*v axis*a axis,
   ∑ axis : Fin 3, (a axis)^2⟩

theorem relative_motion (state : Material frame) (site : BridgeSite state.reference) (time : ℝ) :
    relativePosition (state.movedPositions time) site = relativePosition state.positions site +
      time • relativeVelocity state site + time^2 • relativeQuadratic state site := by
  funext axis
  change
    (state.positions site.phosphate.nuclear axis +
      (time / CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear)*state.momenta site.phosphate.nuclear axis +
      (time^2 / (2*CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear))*state.jointForce site.phosphate.nuclear axis) -
    (state.positions site.oxygenNuclear axis +
      (time / CPS1MolecularFrame.inertia state.reference site.oxygenNuclear)*state.momenta site.oxygenNuclear axis +
      (time^2 / (2*CPS1MolecularFrame.inertia state.reference site.oxygenNuclear))*state.jointForce site.oxygenNuclear axis) =
    (state.positions site.phosphate.nuclear axis-state.positions site.oxygenNuclear axis) +
      time*(state.momenta site.phosphate.nuclear axis / CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear -
        state.momenta site.oxygenNuclear axis / CPS1MolecularFrame.inertia state.reference site.oxygenNuclear) +
      time^2*(state.jointForce site.phosphate.nuclear axis / (2*CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear) -
        state.jointForce site.oxygenNuclear axis / (2*CPS1MolecularFrame.inertia state.reference site.oxygenNuclear))
  simp only [div_eq_mul_inv]
  ring

theorem distance_response (state : Material frame) (site : BridgeSite state.reference) (time : ℝ) :
    squaredDistance (state.movedPositions time) site-squaredDistance state.positions site =
      (distancePolynomial state site).delta time := by
  let r := relativePosition state.positions site
  let v := relativeVelocity state site
  let a := relativeQuadratic state site
  have difference : squaredDistance (state.movedPositions time) site-squaredDistance state.positions site =
      ∑ axis : Fin 3, ((r axis+time*v axis+time^2*a axis)^2-(r axis)^2) := by
    rw [squaredDistance,squaredDistance,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro axis _
    have moved := congrFun (relative_motion state site time) axis
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at moved
    rw [moved]
  rw [difference]
  change _ = (∑ axis : Fin 3, 2*r axis*v axis)*time +
    (∑ axis : Fin 3, ((v axis)^2+2*r axis*a axis))*time^2 +
    (∑ axis : Fin 3, 2*v axis*a axis)*time^3 + (∑ axis : Fin 3, (a axis)^2)*time^4
  simp only [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro axis _
  ring

theorem distance_eventually_signed (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (generated : (distancePolynomial state site).leading? = some degree) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time →
      0 < (distancePolynomial state site).coefficient degree *
        (squaredDistance (state.movedPositions time) site-squaredDistance state.positions site) := by
  filter_upwards [Generic.quartic_eventually_signed (distancePolynomial state site) degree generated] with time signed
  intro positive
  simpa only [distance_response] using signed positive

end
end CPS1AddressedBondResponse
