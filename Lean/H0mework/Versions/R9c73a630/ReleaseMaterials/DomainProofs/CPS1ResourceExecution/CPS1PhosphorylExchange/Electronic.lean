import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Graph
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Integrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Symmetries
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.WholeBasisResponse

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1ElectronicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open scoped BigOperators InnerProductSpace Matrix

abbrev Spatial (nodes : List Body.Node) := Fin (electronCount nodes+1)
abbrev Spin (nodes : List Body.Node) := Spatial nodes × Bool
abbrev Electron (nodes : List Body.Node) := Fin (electronCount nodes)
abbrev Coefficients (nodes : List Body.Node) := Matrix (Spin nodes) (Electron nodes) ℂ

def initialIndex (nodes : List Body.Node) (electron : Electron nodes) : Spin nodes :=
  (⟨electron.val/2,by omega⟩,decide (electron.val%2=1))

def initialOccupation (nodes : List Body.Node) : Coefficients nodes :=
  fun index electron => if index = initialIndex nodes electron then 1 else 0

theorem initial_index_injective (nodes : List Body.Node) : Function.Injective (initialIndex nodes) := by
  intro first second same
  have quotient : first.val/2 = second.val/2 := congrArg (fun index : Spin nodes => index.1.val) same
  have spin : decide (first.val%2=1) = decide (second.val%2=1) :=
    congrArg (fun index : Spin nodes => index.2) same
  have odd : (first.val%2=1) ↔ (second.val%2=1) := by
    exact of_decide_eq_true (show decide ((first.val%2=1) ↔ (second.val%2=1)) = true by simp [spin])
  apply Fin.ext
  omega

theorem initial_occupation_gram (nodes : List Body.Node) :
    (initialOccupation nodes).conjTranspose * initialOccupation nodes = 1 := by
  ext first second
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,initialOccupation,apply_ite star,star_one,star_zero,
    ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [(initial_index_injective nodes).eq_iff,Matrix.one_apply]

def density {nodes : List Body.Node} (occupied : Coefficients nodes) : Matrix (Spin nodes) (Spin nodes) ℂ :=
  occupied*occupied.conjTranspose

def kinetic (nodes : List Body.Node) (mass : ℝ) (i j : Spatial nodes) : ℂ :=
  ((1/(2*mass) : ℝ) : ℂ)*∑ axis : Fin 3,
    inner ℂ (spatialField 0 (electronCount nodes+1) i (Pi.single axis 1))
      (spatialField 0 (electronCount nodes+1) j (Pi.single axis 1))

def attraction (nodes : List Body.Node) (i j : Spatial nodes) : ℂ :=
  ((nucleusNodes nodes).map (fun node => -(node.particle.charge : ℂ)*
    nuclearIntegral 0 (electronCount nodes+1) i j (fun axis => node.row.position axis))).sum

def core (nodes : List Body.Node) (mass : ℝ) : Matrix (Spin nodes) (Spin nodes) ℂ :=
  fun i j => if i.2 = j.2 then kinetic nodes mass i.1 j.1+attraction nodes i.1 j.1 else 0

def twoBody (nodes : List Body.Node) (i j k l : Spin nodes) : ℂ :=
  if i.2 = k.2 ∧ j.2 = l.2 then
    pairIntegral 0 (electronCount nodes+1) i.1 k.1 j.1 l.1 else 0

def fock (nodes : List Body.Node) (mass : ℝ) (occupied : Coefficients nodes) :
    Matrix (Spin nodes) (Spin nodes) ℂ :=
  fun i k => core nodes mass i k+∑ j, ∑ l,
    density occupied l j*(twoBody nodes i j k l-twoBody nodes i j l k)

def electronicEnergy (nodes : List Body.Node) (mass : ℝ) (occupied : Coefficients nodes) : ℝ :=
  (Matrix.trace (core nodes mass*density occupied)).re+(1/2)*
    (∑ i, ∑ j, ∑ k, ∑ l, density occupied k i*density occupied l j*
      (twoBody nodes i j k l-twoBody nodes i j l k)).re

def wholeEnergy (nodes : List Body.Node) (mass : ℝ) (occupied : Coefficients nodes) : ℝ :=
  Body.energy (nucleusNodes nodes)+electronicEnergy nodes mass occupied

def occupiedNext (nodes : List Body.Node) (mass time : ℝ) (occupied : Coefficients nodes) : Coefficients nodes :=
  CPS1ElectronicEvolution.occupiedUpdate (fock nodes mass occupied) (time/2) occupied

def densityKernel (nodes : List Body.Node) (occupied : Coefficients nodes)
    (first second : Body.Point) : ℂ :=
  ∑ spin : Bool, ∑ i : Spatial nodes, ∑ j : Spatial nodes,
    star (spatialValue 0 (electronCount nodes+1) i 0 (fun axis => first axis))*
      density occupied (i,spin) (j,spin)*
      spatialValue 0 (electronCount nodes+1) j 0 (fun axis => second axis)

-- Continuous electronic incidence is carried as data. A molecular label is not
-- used to select a result, and no distance threshold grants a reaction.
def bondWeight (nodes : List Body.Node) (occupied : Coefficients nodes)
    (first second : Body.Point) : ℝ :=
  Complex.normSq (densityKernel nodes occupied first second)

-- The complete source basis has one common transverse Gaussian factor.
-- Keeping it before the occupied sum exposes exact bond response without
-- dropping any occupied, virtual, spin, or density cross term.
def transversePoint (x y z : ℝ) : Body.Point := WithLp.toLp 2 ![x,y,z]

theorem orbital_transverse (mode : Nat) (x y z : ℝ) :
    orbitalValue 0 mode 0 ![x,y,z] =
      (Real.exp (-(y^2+z^2)) : ℂ) * orbitalValue 0 mode 0 ![x,0,0] := by
  simp [orbitalValue,CPS1ElectronicSource.primitive,
    SourceGaussianModel.orbital,
    SourceGaussianModel.value,
    SourceGaussianModel.factor,
    SourceGaussianModel.jetPoly,
    GaussianPrimitive.gaussian,
    Real.exp_add]
  ring

theorem spatial_transverse (n : Nat) (i : Fin n) (x y z : ℝ) :
    spatialValue 0 n i 0 ![x,y,z] =
      (Real.exp (-(y^2+z^2)) : ℂ) * spatialValue 0 n i 0 ![x,0,0] := by
  simp only [spatialValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [orbital_transverse j.val x y z]
  ring

theorem density_kernel_transverse (nodes : List Body.Node) (occupied : Coefficients nodes)
    (px py pz qx qy qz : ℝ) :
    densityKernel nodes occupied (transversePoint px py pz) (transversePoint qx qy qz) =
      ((Real.exp (-(py^2+pz^2)) * Real.exp (-(qy^2+qz^2)) : ℝ) : ℂ) *
        densityKernel nodes occupied (transversePoint px 0 0) (transversePoint qx 0 0) := by
  simp only [densityKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (spatialValue 0 (electronCount nodes+1) i 0 ![px,py,pz]) *
      density occupied (i,spin) (j,spin) * spatialValue 0 (electronCount nodes+1) j 0 ![qx,qy,qz] =
    ((Real.exp (-(py^2+pz^2)) * Real.exp (-(qy^2+qz^2)) : ℝ) : ℂ) *
      (star (spatialValue 0 (electronCount nodes+1) i 0 ![px,0,0]) *
        density occupied (i,spin) (j,spin) * spatialValue 0 (electronCount nodes+1) j 0 ![qx,0,0])
  rw [spatial_transverse _ i px py pz,spatial_transverse _ j qx qy qz]
  simp only [Complex.ofReal_mul,star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

theorem bond_weight_transverse (nodes : List Body.Node) (occupied : Coefficients nodes)
    (px py pz qx qy qz : ℝ) :
    bondWeight nodes occupied (transversePoint px py pz) (transversePoint qx qy qz) =
      (Real.exp (-(py^2+pz^2)) * Real.exp (-(qy^2+qz^2)))^2 *
        bondWeight nodes occupied (transversePoint px 0 0) (transversePoint qx 0 0) := by
  unfold bondWeight
  rw [density_kernel_transverse,Complex.normSq_mul,Complex.normSq_ofReal]
  ring

theorem initial_density_kernel (nodes : List Body.Node) (first second : Body.Point) :
    densityKernel nodes (initialOccupation nodes) first second =
      ∑ electron : Electron nodes,
        star (spatialValue 0 (electronCount nodes+1) (initialIndex nodes electron).1 0 (fun axis => first axis))*
          spatialValue 0 (electronCount nodes+1) (initialIndex nodes electron).1 0 (fun axis => second axis) := by
  let term := fun spin (i j : Spatial nodes) (electron : Electron nodes) =>
    star (spatialValue 0 (electronCount nodes+1) i 0 (fun axis => first axis))*
      initialOccupation nodes (i,spin) electron*star (initialOccupation nodes (j,spin) electron)*
        spatialValue 0 (electronCount nodes+1) j 0 (fun axis => second axis)
  have source : densityKernel nodes (initialOccupation nodes) first second =
      ∑ spin : Bool, ∑ i : Spatial nodes, ∑ j : Spatial nodes, ∑ electron : Electron nodes, term spin i j electron := by
    simp only [densityKernel,density,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro electron _
    dsimp only [term]
    ring
  rw [source]
  calc
    _ = ∑ spin : Bool, ∑ electron : Electron nodes, ∑ i : Spatial nodes, ∑ j : Spatial nodes, term spin i j electron := by
      apply Finset.sum_congr rfl
      intro spin _
      calc
        _ = ∑ i : Spatial nodes, ∑ electron : Electron nodes, ∑ j : Spatial nodes, term spin i j electron :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = ∑ electron : Electron nodes, ∑ spin : Bool, ∑ i : Spatial nodes, ∑ j : Spatial nodes, term spin i j electron :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro electron _
      have each (spin : Bool) : (∑ i : Spatial nodes, ∑ j : Spatial nodes, term spin i j electron) =
          if spin = (initialIndex nodes electron).2 then
            star (spatialValue 0 (electronCount nodes+1) (initialIndex nodes electron).1 0 (fun axis => first axis))*
              spatialValue 0 (electronCount nodes+1) (initialIndex nodes electron).1 0 (fun axis => second axis)
          else 0 := by
        by_cases matching : spin = (initialIndex nodes electron).2
        · simp [term,initialOccupation,Prod.ext_iff,matching]
        · simp [term,initialOccupation,Prod.ext_iff,matching]
      simp only [each,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem spatial_nonzero (n : Nat) (i : Fin n) :
    ∃ point : CPS1ElectronicSource.Point, spatialValue 0 n i 0 point ≠ 0 := by
  classical
  by_contra! absent
  have fieldZero : spatialField 0 n i 0 = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [(spatial_memLp 0 n i 0).coeFn_toLp,
      MeasureTheory.Lp.coeFn_zero ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure CPS1ElectronicSource.Point)] with point actual zero
    exact actual.trans ((absent point).trans zero.symm)
  have normOne := (normalized_orthonormal (0 : CPS1ElectronicSource.Point) n).norm_eq_one i
  rw [← spatial_field_normalized 0 n i,fieldZero,norm_zero] at normOne
  norm_num at normOne

theorem initial_kernel_diagonal (nodes : List Body.Node) (point : Body.Point) :
    (densityKernel nodes (initialOccupation nodes) point point).re =
      ∑ electron : Electron nodes,
        Complex.normSq (spatialValue 0 (electronCount nodes+1) (initialIndex nodes electron).1 0 (fun axis => point axis)) := by
  rw [initial_density_kernel]
  simp only [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  rw [← Complex.ofReal_sum,Complex.ofReal_re]

theorem initial_bond_nonempty (nodes : List Body.Node) (electrons : 0 < electronCount nodes) :
    ∃ point : Body.Point, 0 < bondWeight nodes (initialOccupation nodes) point point := by
  let first : Electron nodes := ⟨0,electrons⟩
  obtain ⟨point,present⟩ := spatial_nonzero (electronCount nodes+1) (initialIndex nodes first).1
  have positive : 0 < (densityKernel nodes (initialOccupation nodes) (WithLp.toLp 2 point) (WithLp.toLp 2 point)).re := by
    rw [initial_kernel_diagonal]
    apply Finset.sum_pos'
    · intro electron _
      exact Complex.normSq_nonneg _
    · refine ⟨first,Finset.mem_univ _,?_⟩
      exact Complex.normSq_pos.mpr present
  refine ⟨WithLp.toLp 2 point,Complex.normSq_pos.mpr ?_⟩
  intro zero
  rw [zero,Complex.zero_re] at positive
  exact (lt_irrefl 0) positive

theorem initial_axis_bond_nonempty (nodes : List Body.Node) (electrons : 0 < electronCount nodes) :
    ∃ x : ℝ, 0 < bondWeight nodes (initialOccupation nodes) (transversePoint x 0 0) (transversePoint x 0 0) := by
  obtain ⟨point,positive⟩ := initial_bond_nonempty nodes electrons
  have coordinates : transversePoint (point 0) (point 1) (point 2) = point := by
    ext axis
    fin_cases axis <;> rfl
  rw [← coordinates,bond_weight_transverse] at positive
  refine ⟨point 0,?_⟩
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)))).mp positive

theorem vertical_bond_order (nodes : List Body.Node) (occupied : Coefficients nodes) (x height : ℝ)
    (positive : 0 < bondWeight nodes occupied (transversePoint x 0 0) (transversePoint x 0 0))
    (above : 0 < height) :
    bondWeight nodes occupied (transversePoint x height 0) (transversePoint x (height+2) 0) <
      bondWeight nodes occupied (transversePoint x height 0) (transversePoint x (height+1) 0) := by
  rw [bond_weight_transverse nodes occupied x height 0 x (height+2) 0,
    bond_weight_transverse nodes occupied x height 0 x (height+1) 0]
  norm_num
  have exponent : -((height+2)^2) < -((height+1)^2) := by nlinarith
  have decreasing : Real.exp (-((height+2)^2)) < Real.exp (-((height+1)^2)) :=
    Real.exp_lt_exp.mpr exponent
  have before : 0 < Real.exp (-(height^2))*Real.exp (-((height+2)^2)) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have ordered : Real.exp (-(height^2))*Real.exp (-((height+2)^2)) <
      Real.exp (-(height^2))*Real.exp (-((height+1)^2)) :=
    mul_lt_mul_of_pos_left decreasing (Real.exp_pos _)
  exact mul_lt_mul_of_pos_right (sq_lt_sq₀ before.le (le_trans before.le ordered.le) |>.mpr ordered) positive

theorem density_kernel_continuous {X : Type} [TopologicalSpace X] (nodes : List Body.Node)
    (occupied : X → Coefficients nodes) (first second : X → Body.Point) (point : X)
    (occupationContinuous : ContinuousAt occupied point) (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second point) :
    ContinuousAt (fun value => densityKernel nodes (occupied value) (first value) (second value)) point := by
  have densityContinuous : ContinuousAt (fun value => density (occupied value)) point :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ point occupationContinuous
      (continuous_id.matrix_conjTranspose.continuousAt.comp occupationContinuous)
  unfold densityKernel
  apply tendsto_finsetSum
  intro spin _
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  have firstPoint : ContinuousAt (fun value axis => first value axis) point := by
    apply continuousAt_pi.mpr
    intro axis
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) axis).continuousAt.comp firstContinuous
  have secondPoint : ContinuousAt (fun value axis => second value axis) point := by
    apply continuousAt_pi.mpr
    intro axis
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) axis).continuousAt.comp secondContinuous
  have coefficient := (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous (i,spin)) (j,spin))
  exact (((spatial_continuous 0 (electronCount nodes+1) i 0).continuousAt.comp firstPoint).star.mul coefficient).mul
    ((spatial_continuous 0 (electronCount nodes+1) j 0).continuousAt.comp secondPoint)

theorem bond_weight_continuous {X : Type} [TopologicalSpace X] (nodes : List Body.Node)
    (occupied : X → Coefficients nodes) (first second : X → Body.Point) (point : X)
    (occupationContinuous : ContinuousAt occupied point) (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second point) :
    ContinuousAt (fun value => bondWeight nodes (occupied value) (first value) (second value)) point := by
  unfold bondWeight
  exact Complex.continuous_normSq.continuousAt.comp
    (density_kernel_continuous nodes occupied first second point occupationContinuous firstContinuous secondContinuous)

structure ElectronicState (nodes : List Body.Node) where
  occupied : Coefficients nodes
  reserve : ℝ

-- Nuclear positions vary on the actual complete source; the electronic index
-- remains tied to that source, so no caller swaps coefficients or coverage.
def attractionAt (source pose : List Body.Node) (i j : Spatial source) : ℂ :=
  ((nucleusNodes pose).map (fun node => -(node.particle.charge : ℂ)*
    nuclearIntegral 0 (electronCount source+1) i j (fun axis => node.row.position axis))).sum

def coreAt (source pose : List Body.Node) (mass : ℝ) : Matrix (Spin source) (Spin source) ℂ :=
  fun i j => if i.2 = j.2 then kinetic source mass i.1 j.1+attractionAt source pose i.1 j.1 else 0

def wholeEnergyAt (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) : ℝ :=
  Body.energy (nucleusNodes pose)+(Matrix.trace (coreAt source pose mass*density occupied)).re+
    (1/2)*(∑ i, ∑ j, ∑ k, ∑ l, density occupied k i*density occupied l j*
      (twoBody source i j k l-twoBody source i j l k)).re

def fockAt (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) :
    Matrix (Spin source) (Spin source) ℂ :=
  fun i k => coreAt source pose mass i k+∑ j, ∑ l,
    density occupied l j*(twoBody source i j k l-twoBody source i j l k)

def occupiedNextAt (source pose : List Body.Node) (mass time : ℝ)
    (occupied : Coefficients source) : Coefficients source :=
  CPS1ElectronicEvolution.occupiedUpdate (fockAt source pose mass occupied) (time/2) occupied

theorem nuclear_integral_differentiable (n : Nat) (i j : Fin n) (position : CPS1ElectronicSource.Point) :
    DifferentiableAt ℝ (CPS1ElectronicSource.nuclearIntegral 0 n i j) position := by
  have expansion : (fun next => CPS1ElectronicSource.nuclearIntegral 0 n i j next) =
      (fun next => ∑ b : Fin n, ∑ a : Fin n, (star (coefficients 0 n a i)*coefficients 0 n b j)*
        CPS1MolecularFrame.primitiveNuclearIntegral 0 0 a.val b.val next 0 0) := by
    funext next
    rw [CPS1QuantumNuclear.normalized_integral_expansion]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    rw [CPS1Deformation.multicentre_nuclear_relative]
  rw [show CPS1ElectronicSource.nuclearIntegral 0 n i j = _ from expansion]
  apply DifferentiableAt.fun_sum
  intro b _
  apply DifferentiableAt.fun_sum
  intro a _
  let selected : CPS1ElectronicSource.Point → Fin 3 → CPS1ElectronicSource.Point := fun next => ![0,0,next]
  have selection : DifferentiableAt ℝ selected position := by
    apply differentiableAt_pi.mpr
    intro index
    fin_cases index
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_id
  have generated := (CPS1Deformation.multicentre_nuclear_hasFDerivAt a.val b.val 0 0 (selected position)).differentiableAt.comp position selection
  exact generated.const_mul _

theorem kinetic_star (nodes : List Body.Node) (mass : ℝ) (i j : Spatial nodes) :
    star (kinetic nodes mass i j) = kinetic nodes mass j i := by
  unfold kinetic
  simp only [Complex.star_def,map_mul,map_sum,Complex.conj_ofReal]
  apply congrArg (fun z : ℂ => ((1/(2*mass) : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro axis _
  exact inner_conj_symm _ _

theorem attraction_at_star (source pose : List Body.Node) (i j : Spatial source) :
    star (attractionAt source pose i j) = attractionAt source pose j i := by
  unfold attractionAt
  induction nucleusNodes pose with
  | nil => simp
  | cons node rest ih =>
    simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_neg]
    rw [ih,CPS1ElectronicSource.nuclear_star]
    have realCharge : star (node.particle.charge : ℂ) = (node.particle.charge : ℂ) := by simp
    rw [realCharge]
    ring

theorem core_at_hermitian (source pose : List Body.Node) (mass : ℝ) :
    (coreAt source pose mass).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases same : i.2 = j.2
  · simp only [coreAt,if_pos same,if_pos same.symm,star_add,kinetic_star,attraction_at_star]
  · simp only [coreAt,if_neg same,if_neg (Ne.symm same),star_zero]

theorem two_body_star (source : List Body.Node) (i j k l : Spin source) :
    star (twoBody source i j k l) = twoBody source k l i j := by
  by_cases same : i.2 = k.2 ∧ j.2 = l.2
  · simp only [twoBody,if_pos same,if_pos (show k.2 = i.2 ∧ l.2 = j.2 from ⟨same.1.symm,same.2.symm⟩),
      CPS1ElectronicSource.pair_star]
  · have reversed : ¬(k.2 = i.2 ∧ l.2 = j.2) := fun h => same ⟨h.1.symm,h.2.symm⟩
    simp only [twoBody,if_neg same,if_neg reversed,star_zero]

theorem two_body_swap (source : List Body.Node) (i j k l : Spin source) :
    twoBody source i j k l = twoBody source j i l k := by
  by_cases same : i.2 = k.2 ∧ j.2 = l.2
  · simp only [twoBody,if_pos same,if_pos (show j.2 = l.2 ∧ i.2 = k.2 from ⟨same.2,same.1⟩)]
    exact CPS1ElectronicSource.pair_swap _ _ _ _ _ _
  · have reversed : ¬(j.2 = l.2 ∧ i.2 = k.2) := fun h => same ⟨h.2,h.1⟩
    simp only [twoBody,if_neg same,if_neg reversed]

theorem fock_at_hermitian (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) :
    (fockAt source pose mass occupied).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (coreAt source pose mass k i) = coreAt source pose mass i k :=
    (core_at_hermitian source pose mass).apply i k
  have densityStar (j l : Spin source) : star (density occupied l j) = density occupied j l :=
    (Matrix.isHermitian_mul_conjTranspose_self occupied).apply j l
  simp only [fockAt,star_add,star_sum,star_mul,star_sub,coreStar,densityStar,two_body_star]
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => coreAt source pose mass i k + z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [two_body_swap source j i k l]
  ring

theorem fock_at_occupation_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node)
    (mass : ℝ) (occupied : X → Coefficients source) (point : X) (actual : ContinuousAt occupied point) :
    ContinuousAt (fun value => fockAt source pose mass (occupied value)) point := by
  have densityContinuous : ContinuousAt (fun value => density (occupied value)) point :=
    CPS1PositivePulse.matrix_mul_continuousAt _ _ point actual
      (continuous_id.matrix_conjTranspose.continuousAt.comp actual)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  unfold fockAt
  apply ContinuousAt.add continuousAt_const
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro l _
  exact (continuousAt_pi.mp (continuousAt_pi.mp densityContinuous l) j).mul_const _

theorem occupied_next_continuous {X : Type} [TopologicalSpace X] (source pose : List Body.Node) (mass : ℝ)
    (time : X → ℝ) (occupied : X → Coefficients source) (point : X)
    (timeContinuous : ContinuousAt time point) (occupationContinuous : ContinuousAt occupied point) :
    ContinuousAt (fun value => occupiedNextAt source pose mass (time value) (occupied value)) point :=
  CPS1PositivePulse.occupied_update_continuousAt (fun value => fockAt source pose mass (occupied value))
    (fun value => time value/2) occupied point
    (fock_at_occupation_continuous source pose mass occupied point occupationContinuous)
    (timeContinuous.div_const 2) occupationContinuous (fock_at_hermitian source pose mass (occupied point))

theorem occupied_next_zero (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) :
    occupiedNextAt source pose mass 0 occupied = occupied := by
  simp only [occupiedNextAt,zero_div,CPS1ElectronicEvolution.occupiedUpdate,CPS1ElectronicEvolution.zero_time,Matrix.one_mul]

theorem occupied_next_gram (source pose : List Body.Node) (mass time : ℝ) (occupied : Coefficients source) :
    (occupiedNextAt source pose mass time occupied).conjTranspose * occupiedNextAt source pose mass time occupied =
      occupied.conjTranspose * occupied :=
  CPS1ElectronicEvolution.occupied_gram _ (fock_at_hermitian source pose mass occupied) (time/2) occupied

theorem electron_number (source : List Body.Node) (occupied : Coefficients source)
    (orthogonal : occupied.conjTranspose * occupied = 1) :
    Matrix.trace (density occupied) = (electronCount source : ℂ) := by
  rw [density,Matrix.trace_mul_comm,orthogonal]
  simp only [Matrix.trace_one,Fintype.card_fin]

def densityKernelAt (source : List Body.Node) (occupied : Coefficients source)
    (first second : Body.Point) : ℂ := densityKernel source occupied first second

def capture (nodes : List Body.Node) (mass reserve : ℝ) : Except Failure (ElectronicState nodes) := by
  classical
  let occupied := initialOccupation nodes
  let price := wholeEnergy nodes mass occupied-Body.energy nodes
  exact if reserve < 0 then .error .negativeReserve else if reserve < price then .error .captureShortage
    else .ok ⟨occupied,reserve-price⟩

theorem whole_energy_at_self (nodes : List Body.Node) (mass : ℝ) (occupied : Coefficients nodes) :
    wholeEnergyAt nodes nodes mass occupied = wholeEnergy nodes mass occupied := by
  have equalCore : coreAt nodes nodes mass = core nodes mass := by
    funext i j
    rfl
  unfold wholeEnergyAt wholeEnergy electronicEnergy
  rw [equalCore]
  ring

theorem captured_account (nodes : List Body.Node) (mass reserve : ℝ) (state : ElectronicState nodes)
    (actual : capture nodes mass reserve = .ok state) :
    state.occupied = initialOccupation nodes ∧
    wholeEnergy nodes mass state.occupied+state.reserve = Body.energy nodes+reserve := by
  unfold capture at actual
  dsimp only at actual
  split at actual
  · cases actual
  · split at actual
    · cases actual
    · cases Except.ok.inj actual
      refine ⟨rfl,?_⟩
      dsimp only
      ring

def electronicPulse (nodes : List Body.Node) (mass time : ℝ) (before : ElectronicState nodes) :
    Except Failure (ElectronicState nodes) := by
  classical
  let occupied := occupiedNext nodes mass time before.occupied
  let price := wholeEnergy nodes mass occupied-wholeEnergy nodes mass before.occupied
  exact if time ≤ 0 then .error .nonpositiveTime else if before.reserve < price then .error .energyShortage
    else .ok ⟨occupied,before.reserve-price⟩

end
end CPS1PhosphorylExchange
