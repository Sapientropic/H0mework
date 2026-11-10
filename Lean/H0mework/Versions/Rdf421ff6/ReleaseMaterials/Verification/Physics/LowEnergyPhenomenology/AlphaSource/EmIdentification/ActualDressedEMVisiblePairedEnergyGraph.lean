import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMVisibleLeftSelector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualDressedEMTaylorPoleFlux ActualDressedEMClockDispersion ActualDressedEMQuantumThreshold ActualDressedEMPolePairEnergy ActualDressedEMFullPoleFlux ActualDressedEMPhysicalResidueFlux
open ActualDressedEMSourceTransport ActualEMCarrierOwn
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] correctedPhysicalClock correctedPhysicalClockJet emInsertion
  emPhysicalCorrectedPoleCoefficient emPhysicalNormalizedPoleColumnCoefficient emFullPhysicalResidue
  emFullColumnPoleOrder emPairedAnalyticColumn emFullRowPoleOrder

/-- Original frequency derivatives of the left mode are retained alongside its sigma feedback. -/
def emLeftFrequencyChain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  ∑p∈(Finset.HasAntidiagonal.antidiagonal r).erase (0,r),
    (emPhysicalCorrectedPoleCoefficient event eps n a p.1).transpose*ᵥ
      emPhysicalLeftPoleCoefficient event eps n mu a p.2

def emCompleteLeftDefect (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu : Fin 4) (a : ℂ) (r : ℕ) : Fin 289→ℂ :=
  emPhysicalLeftClockDefectCoefficient event eps n mu a r+emLeftFrequencyChain event eps n mu a r

private theorem split_coefficient {ι : Type*} [Fintype ι]
    (P : ℕ→Matrix ι ι ℂ) (L : ℕ→ι→ℂ) (B : ι→ℂ) (r : ℕ)
    (source : ∀i,(∑j,∑p∈Finset.HasAntidiagonal.antidiagonal r,P p.1 j i*L p.2 j)+B i=0) :
    (P 0).transpose*ᵥL r=-(B+∑p∈(Finset.HasAntidiagonal.antidiagonal r).erase (0,r),
      (P p.1).transpose*ᵥL p.2) := by
  funext i
  have coefficient := source i
  rw [Finset.sum_comm] at coefficient
  have member : (0,r)∈Finset.HasAntidiagonal.antidiagonal r := by simp
  rw [←Finset.sum_erase_add _ _ member] at coefficient
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.neg_apply,Pi.add_apply,Finset.sum_apply]
  linear_combination coefficient

/-- The source-selected lower left mode has an explicit complete defect, rather than a caller kernel assumption. -/
theorem actual_em_complete_left_defect (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (r : ℕ) (lower : r<emFullRowPoleOrder event eps n mu (s : ℂ)) :
    (correctedPhysicalClock event eps (sourceFrequency eps s) n).transpose*ᵥ
      emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r=
      -emCompleteLeftDefect event eps n mu (s : ℂ) r := by
  have source := split_coefficient (emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ))
    (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ))
    (emPhysicalLeftClockDefectCoefficient event eps n mu (s : ℂ) r) r
    (actual_em_physical_lower_left_chain event eps n mu nu (s : ℂ) regular root r lower)
  rw [actual_em_physical_pole_clock_zero event eps s n eps_ne regular] at source
  exact source

private theorem paired_matrix_read {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) (l v : ι→ℂ) :
    dotProduct l (P*ᵥv)=dotProduct (P.transpose*ᵥl) v := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def emVisiblePairedClockEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ))

def emVisiblePairedHigherEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (∑k∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
      emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (k+2)*ᵥ
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ)
          (emFullColumnPoleOrder event eps n nu (s : ℂ)-(k+2)))

def emVisiblePairedSourceInput (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r) (fun i => emInsertion i nu)

def emVisiblePairedAnalyticDebt (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℂ :=
  dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) (emPairedAnalyticColumn event eps n nu (s : ℂ))

/-- All right pole orders and both source-generated left defects enter the physical paired energy. -/
theorem actual_em_visible_paired_energy_balance (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (r : ℕ) (lower : r<emFullRowPoleOrder event eps n mu (s : ℂ)) :
    emVisiblePairedClockEnergy event eps s n mu nu r+emVisiblePairedHigherEnergy event eps s n mu nu r=
      emVisiblePairedSourceInput event eps s n mu nu r+emVisiblePairedAnalyticDebt event eps s n mu nu r := by
  have full := actual_em_original_physical_residue_balance event eps s n mu nu eps_ne balanced finite regular root
  have projected := congrArg (dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)) full
  rw [dotProduct_add,dotProduct_add,paired_matrix_read,
    actual_em_complete_left_defect event eps s n mu nu eps_ne regular root r lower,neg_dotProduct] at projected
  have analytic : emPairedAnalyticColumn event eps n nu (s : ℂ)=
      (fun i => (emFullAnalyticColumnNumerator event eps n nu (s : ℂ) i).eval (s : ℂ)/
        (emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ)) := by unfold emPairedAnalyticColumn;rfl
  rw [←analytic] at projected
  have priced : -emVisiblePairedAnalyticDebt event eps s n mu nu r+emVisiblePairedClockEnergy event eps s n mu nu r+
      emVisiblePairedHigherEnergy event eps s n mu nu r=emVisiblePairedSourceInput event eps s n mu nu r := projected
  linear_combination priced

/-- This whole source flux retains all corrections and is normalized by its generated nonzero detector read. -/
theorem actual_em_visible_whole_energy_nonzero (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let r := emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root
    emVisiblePairedClockEnergy event eps s n mu nu r+emVisiblePairedHigherEnergy event eps s n mu nu r-
      emVisiblePairedAnalyticDebt event eps s n mu nu r=emVisiblePairedSourceInput event eps s n mu nu r ∧
    emVisiblePairedSourceInput event eps s n mu nu r≠0 := by
  dsimp only
  have spec := actual_em_visible_left_selector_spec event eps n mu nu (s : ℂ) eps_ne root
  have balance := actual_em_visible_paired_energy_balance event eps s n mu nu eps_ne balanced finite regular root _ spec.1
  refine ⟨by linear_combination balance,?_⟩
  simpa only [emVisiblePairedSourceInput,dotProduct,mul_comm] using spec.2

theorem actual_em_visible_whole_energy_unit (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let r := emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root
    emVisiblePairedClockEnergy event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r+
      emVisiblePairedHigherEnergy event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r-
      emVisiblePairedAnalyticDebt event eps s n mu nu r/emVisiblePairedSourceInput event eps s n mu nu r=1 := by
  dsimp only
  obtain ⟨balance,nonzero⟩ := actual_em_visible_whole_energy_nonzero event eps s n mu nu eps_ne balanced finite regular root
  rw [←add_div,←sub_div,balance,div_self nonzero]

/-- This price is evaluated from the original higher pole flux and the full analytic defect; it does not define a coupling difference. -/
def emVisibleClockGraphPrice (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℝ :=
  ‖emVisiblePairedHigherEnergy event eps s n mu nu r‖+‖emVisiblePairedAnalyticDebt event eps s n mu nu r‖

private theorem norm_graph_price (Gamma Higher Debt Input : ℂ) (source : Gamma+Higher=Input+Debt) :
    ‖Input‖-(‖Higher‖+‖Debt‖)≤‖Gamma‖ := by
  have same : Input=Gamma+(Higher-Debt) := by linear_combination -source
  have bound : ‖Input‖≤‖Gamma‖+(‖Higher‖+‖Debt‖) := by
    rw [same]
    calc
      _≤‖Gamma‖+‖Higher-Debt‖ := norm_add_le _ _
      _≤_ := by gcongr;exact norm_sub_le _ _
  linarith

/-- A source-computed graph price produces a nondegenerate actual clock-energy chart. -/
theorem actual_em_visible_clock_graph_bound (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let r := emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root
    ‖emVisiblePairedSourceInput event eps s n mu nu r‖-emVisibleClockGraphPrice event eps s n mu nu r≤
      ‖emVisiblePairedClockEnergy event eps s n mu nu r‖ := by
  dsimp only
  have spec := actual_em_visible_left_selector_spec event eps n mu nu (s : ℂ) eps_ne root
  exact norm_graph_price _ _ _ _
    (actual_em_visible_paired_energy_balance event eps s n mu nu eps_ne balanced finite regular root _ spec.1)

theorem actual_em_visible_clock_graph_nondegenerate (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (priced : emVisibleClockGraphPrice event eps s n mu nu
      (emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root)<
        ‖emVisiblePairedSourceInput event eps s n mu nu (emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root)‖) :
    emVisiblePairedClockEnergy event eps s n mu nu
      (emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root)≠0 := by
  have bound := actual_em_visible_clock_graph_bound event eps s n mu nu eps_ne balanced finite regular root
  dsimp only at bound
  intro zero
  rw [zero,norm_zero] at bound
  linarith

def emVisibleEnergyNormalizedResidue (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : Fin 289→ℂ :=
  (emVisiblePairedClockEnergy event eps s n mu nu r)⁻¹ • emFullPhysicalResidue event eps n nu (s : ℂ)

def emVisiblePairedSpatialEnergy (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ) : ℂ :=
  -(eps^2 : ℂ)⁻¹*dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥ
      emFullPhysicalResidue event eps n nu (s : ℂ))

/-- Actual higher/defect pricing generates this clock normalization without a nonzero-energy premise. -/
theorem actual_em_visible_clock_unit_from_price (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (priced : emVisibleClockGraphPrice event eps s n mu nu
      (emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root)<
        ‖emVisiblePairedSourceInput event eps s n mu nu (emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root)‖) :
    let r := emVisibleLeftSelector event eps n mu nu (s : ℂ) eps_ne root
    dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
      (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥ
        emVisibleEnergyNormalizedResidue event eps s n mu nu r)=1 := by
  dsimp only
  rw [emVisibleEnergyNormalizedResidue,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  exact inv_mul_cancel₀ (actual_em_visible_clock_graph_nondegenerate event eps s n mu nu eps_ne balanced finite regular root priced)

/-- Both derivatives are read in the original physical clock/spatial units; this ratio retains its pole/branch identification responsibility. -/
theorem actual_em_visible_energy_normalized_spatial_read (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) :
    -(eps^2 : ℂ)⁻¹*dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
      (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥ
        emVisibleEnergyNormalizedResidue event eps s n mu nu r)=
      emVisiblePairedSpatialEnergy event eps s n delta mu nu r/emVisiblePairedClockEnergy event eps s n mu nu r := by
  rw [emVisibleEnergyNormalizedResidue,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  unfold emVisiblePairedSpatialEnergy
  ring

/-- The complete lower right pole chain is the actual residue's inhomogeneous operator read. -/
def emRightResidueDefect (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  ∑p∈(Finset.HasAntidiagonal.antidiagonal (emFullColumnPoleOrder event eps n nu a-1)).erase
    (0,emFullColumnPoleOrder event eps n nu a-1),
    emPhysicalCorrectedPoleCoefficient event eps n a p.1*ᵥ
      emPhysicalNormalizedPoleColumnCoefficient event eps n nu a p.2

private theorem split_right_coefficient {ι : Type*} [Fintype ι]
    (P : ℕ→Matrix ι ι ℂ) (V : ℕ→ι→ℂ) (k : ℕ)
    (source : ∀i,(∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,P p.1 i j*V p.2 j)=0) :
    P 0*ᵥV k=-(∑p∈(Finset.HasAntidiagonal.antidiagonal k).erase (0,k),P p.1*ᵥV p.2) := by
  funext i
  have coefficient := source i
  rw [Finset.sum_comm] at coefficient
  have member : (0,k)∈Finset.HasAntidiagonal.antidiagonal k := by simp
  rw [←Finset.sum_erase_add _ _ member] at coefficient
  simp only [Matrix.mulVec,dotProduct,Pi.neg_apply,Finset.sum_apply]
  linear_combination coefficient

theorem actual_em_right_residue_defect (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    correctedPhysicalClock event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)=
      -emRightResidueDefect event eps n nu (s : ℂ) := by
  have positive := source_em_full_pole_order_positive event eps n mu nu (s : ℂ) root
  have source := split_right_coefficient (emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ))
    (emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ))
    (emFullColumnPoleOrder event eps n nu (s : ℂ)-1)
    (actual_em_physical_lower_pole_chain event eps n mu nu (s : ℂ) balanced finite regular root _ (by omega))
  rw [actual_em_physical_pole_clock_zero event eps s n eps_ne regular,
    source_em_physical_canonical_residue event eps n mu nu (s : ℂ) eps_ne root] at source
  exact source

private theorem moving_pair_derivative {ι : Type*} [Fintype ι]
    (P : ℝ→Matrix ι ι ℂ) (l v : ℝ→ι→ℂ) (P' : Matrix ι ι ℂ) (l' v' : ι→ℂ) (x : ℝ)
    (op : HasDerivAt P P' x) (left : HasDerivAt l l' x) (right : HasDerivAt v v' x) :
    HasDerivAt (fun t => dotProduct (l t) (P t*ᵥv t))
      (dotProduct l' (P x*ᵥv x)+dotProduct (l x) (P'*ᵥv x)+dotProduct (l x) (P x*ᵥv')) x := by
  simp only [Matrix.mulVec,dotProduct]
  have generated : HasDerivAt (fun t => ∑i,∑j,l t i*(P t i j*v t j))
      (∑i,∑j,(l' i*(P x i j*v x j)+l x i*(P' i j*v x j+P x i j*v' j))) x := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hasDerivAt_pi.mp left) i).fun_mul
      (((hasDerivAt_pi.mp ((hasDerivAt_pi.mp op) i)) j).fun_mul ((hasDerivAt_pi.mp right) j))
  simp only [Finset.mul_sum]
  convert generated using 1
  simp only [mul_add,Finset.sum_add_distrib]
  ring

/-- Moving modes preserve both source-generated defects. This consumes differentiable modes and does not generate a root branch. -/
theorem actual_em_visible_moving_clock_read (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (r : ℕ) (lower : r<emFullRowPoleOrder event eps n mu (s : ℂ))
    (l v : ℝ→Fin 289→ℂ) (l' v' : Fin 289→ℂ)
    (leftPoint : l (sourceFrequency eps s)=emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (rightPoint : v (sourceFrequency eps s)=emFullPhysicalResidue event eps n nu (s : ℂ))
    (left : HasDerivAt l l' (sourceFrequency eps s)) (right : HasDerivAt v v' (sourceFrequency eps s)) :
    HasDerivAt (fun omega => dotProduct (l omega) (correctedPhysicalClock event eps omega n*ᵥv omega))
      (emVisiblePairedClockEnergy event eps s n mu nu r-
        dotProduct l' (emRightResidueDefect event eps n nu (s : ℂ))-
          dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) v') (sourceFrequency eps s) := by
  have point : sourceFrequency eps s/eps^2=s := by
    unfold sourceFrequency
    exact mul_div_cancel_left₀ s (pow_ne_zero 2 eps_ne)
  have generated := moving_pair_derivative (fun omega => correctedPhysicalClock event eps omega n)
    l v (correctedPhysicalClockJet event eps (sourceFrequency eps s) n) l' v' (sourceFrequency eps s)
    (actual_corrected_physical_clock_derivative event eps (sourceFrequency eps s) n eps_ne
      (by simpa only [point] using regular)) left right
  rw [leftPoint,rightPoint,actual_em_right_residue_defect event eps s n mu nu eps_ne balanced finite regular root,
    dotProduct_neg,paired_matrix_read (correctedPhysicalClock event eps (sourceFrequency eps s) n),
    actual_em_complete_left_defect event eps s n mu nu eps_ne regular root r lower,neg_dotProduct] at generated
  have same : -dotProduct l' (emRightResidueDefect event eps n nu (s : ℂ))+
      dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
        (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ))+
      -dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) v'=
      emVisiblePairedClockEnergy event eps s n mu nu r-
        dotProduct l' (emRightResidueDefect event eps n nu (s : ℂ))-
          dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) v' := by
    unfold emVisiblePairedClockEnergy
    ring
  rw [same] at generated
  exact generated

/-- Spatial transport retains the moving paired-mode terms and the original eps² physical momentum scale. -/
theorem actual_em_visible_moving_spatial_read (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (spatialRegular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0
      ((sourceFrequency eps s/eps^2 : ℝ) : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (r : ℕ) (lower : r<emFullRowPoleOrder event eps n mu (s : ℂ))
    (l v : ℝ→Fin 289→ℂ) (l' v' : Fin 289→ℂ)
    (leftPoint : l 0=emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
    (rightPoint : v 0=emFullPhysicalResidue event eps n nu (s : ℂ))
    (left : HasDerivAt l l' 0) (right : HasDerivAt v v' 0) :
    HasDerivAt (fun t => dotProduct (l t)
      (correctedPhysicalClock event eps (sourceFrequency eps s) (sourceTangentMomentum n delta t)*ᵥv t))
      (-(eps^2 : ℂ)*emVisiblePairedSpatialEnergy event eps s n delta mu nu r-
        dotProduct l' (emRightResidueDefect event eps n nu (s : ℂ))-
          dotProduct (emCompleteLeftDefect event eps n mu (s : ℂ) r) v') 0 := by
  have generated := moving_pair_derivative
    (fun t => correctedPhysicalClock event eps (sourceFrequency eps s) (sourceTangentMomentum n delta t))
    l v (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta) l' v' 0
    (actual_corrected_physical_spatial_derivative event eps (sourceFrequency eps s) n delta eps_ne spatialRegular) left right
  have momentum : sourceTangentMomentum n delta 0=n := by simp only [sourceTangentMomentum,zero_smul,add_zero]
  rw [leftPoint,rightPoint,momentum,
    actual_em_right_residue_defect event eps s n mu nu eps_ne balanced finite regular root,
    dotProduct_neg,paired_matrix_read (correctedPhysicalClock event eps (sourceFrequency eps s) n),
    actual_em_complete_left_defect event eps s n mu nu eps_ne regular root r lower,neg_dotProduct] at generated
  have beta : (eps^2 : ℂ)≠0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr eps_ne)
  have factor : dotProduct (emPhysicalLeftPoleCoefficient event eps n mu (s : ℂ) r)
      (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥemFullPhysicalResidue event eps n nu (s : ℂ))=
        -(eps^2 : ℂ)*emVisiblePairedSpatialEnergy event eps s n delta mu nu r := by
    unfold emVisiblePairedSpatialEnergy
    simp only [neg_mul,mul_neg,neg_neg,←mul_assoc,mul_inv_cancel₀ beta,one_mul]
  rw [factor] at generated
  convert generated using 1
  ring

/-- The complete Noether tensor is retained in the generated whole-energy read unit. -/
def emVisibleWholeEnergyTensor (event : DressedEvent) (eps s : ℝ) (poleMomentum n : PhysicalMomentum)
    (mu nu : Fin 4) (r : ℕ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (emVisiblePairedSourceInput event eps s poleMomentum mu nu r)⁻¹ • actualSourceCoulombTensor event n

theorem actual_em_visible_whole_energy_tensor_derivative (event : DressedEvent) (eps s : ℝ)
    (poleMomentum n delta : PhysicalMomentum) (mu nu : Fin 4) (r : ℕ)
    (regular : ActualDressedAngularSpherePrice.directionLeadingRead event n≠0) :
    HasDerivAt (fun t : ℝ => emVisibleWholeEnergyTensor event eps s poleMomentum
      (sourceTangentMomentum n delta t) mu nu r)
      ((emVisiblePairedSourceInput event eps s poleMomentum mu nu r)⁻¹ • sourceCoulombTensorSpatialJet event n delta) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have entry := (hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (actual_source_coulomb_tensor_spatial_derivative event n delta regular) i)) j
  simpa only [emVisibleWholeEnergyTensor,Matrix.smul_apply,smul_eq_mul] using
    entry.const_mul (emVisiblePairedSourceInput event eps s poleMomentum mu nu r)⁻¹

/-- The source-generated nonzero visible read preserves the whole tensor-gradient responsibility, including degenerate clock energy. -/
theorem actual_em_visible_tensor_gradient_condition (event : DressedEvent) (eps s : ℝ) (poleMomentum n delta : PhysicalMomentum)
    (mu nu : Fin 4) (eps_ne : eps≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps poleMomentum mu nu)) :
    let r := emVisibleLeftSelector event eps poleMomentum mu nu (s : ℂ) eps_ne root
    ((emVisiblePairedSourceInput event eps s poleMomentum mu nu r)⁻¹ • sourceCoulombTensorSpatialJet event n delta)=0 ↔
      sourceCoulombTensorSpatialJet event n delta=0 := by
  dsimp only
  have spec := actual_em_visible_left_selector_spec event eps poleMomentum mu nu (s : ℂ) eps_ne root
  have nonzero : emVisiblePairedSourceInput event eps s poleMomentum mu nu
      (emVisibleLeftSelector event eps poleMomentum mu nu (s : ℂ) eps_ne root)≠0 := by
    simpa only [emVisiblePairedSourceInput,dotProduct,mul_comm] using spec.2
  simp only [smul_eq_zero,inv_eq_zero,nonzero,false_or]

end LowEnergy.GaussComposite.ActualDressedEMVisiblePoleTransport
