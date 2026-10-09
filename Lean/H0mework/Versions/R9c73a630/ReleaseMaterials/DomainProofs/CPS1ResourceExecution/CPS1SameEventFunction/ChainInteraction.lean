import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Differential

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ElectronicSource CPS1ReactiveField.Carried CPS1AtomicDynamics CPS1ReactiveNuclear
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

def isEnzyme : Key root → Bool
  | .enzyme _ => true
  | _ => false

-- Enzyme and complement are restrictions of one source field. A density term
-- is enzyme-supported when either of its exact primitive origins is enzyme.
-- Signed cross terms are retained; this is not a standalone enzyme density.
def enzymePair (germ : Germ root state) (p q : state.PrimitiveIndex) : Bool :=
  isEnzyme (germ.birth.primitiveKey p) || isEnzyme (germ.birth.primitiveKey q)

def chainNuclearEnergy (germ : Germ root state) (charge : ℝ) (position : Point) : ℝ :=
  ((List.finRange state.nuclei.length).map (fun slot =>
    if isEnzyme (germ.nuclearId slot).val then
      Coulomb.pairEnergy charge ((state.nuclei.get slot).particle.charge : ℝ)
        (euclideanPoint position) (state.nuclei.get slot).row.position
    else 0)).sum

def chainElectronEnergy (germ : Germ root state) (charge : ℝ) (position : Point) : ℝ :=
  (∑ electron, ∑ spin : Bool, ∑ p, ∑ q,
    if enzymePair germ p q then
      -(charge : ℂ) * (star (state.occupied p electron) * state.occupied q electron *
        state.nuclearIntegral p q spin position)
    else 0).re

def chainEnergy (germ : Germ root state) (charge : ℝ) (position : Point) : ℝ :=
  chainNuclearEnergy germ charge position+chainElectronEnergy germ charge position

def complementaryEnergy (germ : Germ root state) (charge : ℝ) (position : Point) : ℝ :=
  externalEnergy state charge position-chainEnergy germ charge position

def chainForce (germ : Germ root state) (node : Body.Node) : Body.Point :=
  euclideanPoint (fun axis => -(fderiv ℝ (chainEnergy germ (node.particle.charge : ℝ))
    (fun coordinate => node.row.position coordinate) (Pi.single axis 1)))

def complementaryForce (germ : Germ root state) (node : Body.Node) : Body.Point :=
  externalForce state node-chainForce germ node

theorem whole_field_partition (germ : Germ root state) (charge : ℝ) (position : Point) :
    chainEnergy germ charge position+complementaryEnergy germ charge position =
      externalEnergy state charge position := by
  unfold complementaryEnergy
  ring

theorem chain_electron_differentiable (germ : Germ root state) (charge : ℝ) (position : Point) :
    DifferentiableAt ℝ (chainElectronEnergy germ charge) position := by
  unfold chainElectronEnergy
  apply Complex.reCLM.differentiableAt.comp position
  apply DifferentiableAt.fun_sum
  intro electron _
  apply DifferentiableAt.fun_sum
  intro spin _
  apply DifferentiableAt.fun_sum
  intro p _
  apply DifferentiableAt.fun_sum
  intro q _
  by_cases supported : enzymePair germ p q = true
  · simp only [supported,if_true]
    exact ((external_kernel_differentiable state p q spin position).const_mul _).const_mul _
  · simp only [supported]
    exact differentiableAt_const 0

theorem chain_energy_differentiable (germ : Germ root state) (charge : ℝ) (position : Point)
    (separated : ∀ old ∈ state.nuclei, euclideanPoint position ≠ old.row.position) :
    DifferentiableAt ℝ (chainEnergy germ charge) position := by
  apply DifferentiableAt.add _ (chain_electron_differentiable germ charge position)
  apply CPS1Deformation.differentiable_list_sum (List.finRange state.nuclei.length)
  intro slot _
  by_cases supported : isEnzyme (germ.nuclearId slot).val = true
  · simp only [supported,if_true]
    have distinct := separated (state.nuclei.get slot) (List.get_mem _ _)
    exact ((Coulomb.pair_energy_derivative charge ((state.nuclei.get slot).particle.charge : ℝ)
      (euclideanPoint position) (state.nuclei.get slot).row.position distinct).comp position
        CPS1Deformation.pointDifferential.hasFDerivAt).differentiableAt
  · simp only [supported]
    exact differentiableAt_const 0

-- The independent response reads the actual two material states. Packet and
-- complementary-field impulses are removed to recover the enzyme-supported part.
def independentChainImpulse (germ : Germ root state) (before after : Body.Node)
    (nodes : List Body.Node) (time : ℝ) : Body.Point :=
  independentImpulse before after nodes time-time • complementaryForce germ before

theorem chain_response_generated (germ : Germ root state) (nodes : List Body.Node)
    (time : ℝ) (node : Body.Node) :
    independentChainImpulse germ node (sourceKick state nodes time node) nodes time =
      time • chainForce germ node := by
  rw [independentChainImpulse,independent_response_generated]
  simp only [complementaryForce,smul_sub]
  abel

theorem chain_response_nonzero (germ : Germ root state) (nodes : List Body.Node)
    (time : ℝ) (node : Body.Node) (elapsed : time ≠ 0) (action : chainForce germ node ≠ 0) :
    independentChainImpulse germ node (sourceKick state nodes time node) nodes time ≠ 0 := by
  rw [chain_response_generated]
  exact smul_ne_zero elapsed action

end
end CPS1SameEventFunction
