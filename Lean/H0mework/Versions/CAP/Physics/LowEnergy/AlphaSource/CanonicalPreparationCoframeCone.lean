import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCone

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationPhaseScalar
open SaturationMonoid.PhysicsCore
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumScalarChart
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential GaussLiveMomentum GaussHistoryHilbert
open scoped BigOperators Matrix RealInnerProductSpace

def coframeSlot (i : Fin 6) : Fin 100 := ⟨i.val,by omega⟩

theorem coframe_direction_coordinates (i : Fin 6) :
    fullCoordinates (GaussCoframeCore.coframeDirection i)=Pi.single (coframeSlot i) 1 := by
  rw [full_blocks]
  change joinCoordinates (coframeCoordinates (EuclideanSpace.single i 1),
    read61 (scalarRealify (0 : Scalar)),gaugeFree (0 : coordinateSlice))=_
  have coframe : coframeCoordinates (EuclideanSpace.single i 1)=Pi.single i 1 := by
    change WithLp.ofLp (PiLp.single 2 i 1)=_
    exact PiLp.ofLp_single 2 i 1
  have scalarZero : read61 (scalarRealify (0 : Scalar))=0 := by
    simp [read61,scalarRealify,scalarRead]
  rw [coframe,scalarZero,map_zero]
  ext j
  by_cases small : j.val<6
  · by_cases equal : i.val=j.val
    · have hi : i=⟨j.val,small⟩ := Fin.ext equal
      simp [joinCoordinates,small,coframeSlot,equal]
      rw [← hi]
      simp
    · have hi : i≠⟨j.val,small⟩ := by intro h; exact equal (congrArg Fin.val h)
      have hj : coframeSlot i≠j := by intro h; exact equal (congrArg Fin.val h)
      simp [joinCoordinates,small,hi,hj]
  · have different : coframeSlot i≠j := by
      intro h
      have e:=congrArg Fin.val h
      change i.val=j.val at e
      omega
    simp [joinCoordinates,small,different]

theorem native_coframe_momentum (u : FlatConfiguration) (i : Fin 6) :
    coframeMomentum (nativeCovector (WithLp.toLp 2 u)) i=u (coframeSlot i) := by
  rw [coframeMomentum,nativeCovector_apply,coframe_direction_coordinates]
  simp [Pi.single_apply]

def qCenter (i : Fin 6) : ℝ := if i=0 ∨ i=2 ∨ i=5 then 1 else 0

theorem original_q_center (i : Fin 6) : flatSource (coframeSlot i)=qCenter i := by
  fin_cases i <;> norm_num [flatSource,coframeSlot,qCenter,Fin.ext_iff]

theorem coframe_box (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (i : Fin 6) :
    |(fullCoordinates.symm z).1 i-qCenter i|≤ sourceRadius := by
  have bound:=box (coframeSlot i)
  rw [original_q_center] at bound
  rw [decoded_coframe]
  exact bound

theorem coframe_box_abs (z : FlatConfiguration)
    (box : ∀ i, |z i-flatSource i|≤ sourceRadius) (i : Fin 6) :
    |(fullCoordinates.symm z).1 i|≤2 := by
  have center : |qCenter i|≤1 := by unfold qCenter; split_ifs <;> norm_num
  have bound := abs_le.mp (coframe_box z box i)
  have source:=abs_le.mp center
  rw [abs_le]
  constructor <;> linarith [radius_small.2]

theorem unit_coordinate_abs (u : FlatConfiguration) (unit : (∑ i : Fin 100,u i^2)=1) (i : Fin 100) :
    |u i|≤1 := by
  have square := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 100))) => sq_nonneg (u j))
    (Finset.mem_univ i)
  rw [unit] at square
  nlinarith [sq_abs (u i),abs_nonneg (u i)]

def diagonalIndex (i : Fin 6) : Prop := i=0 ∨ i=2 ∨ i=5
instance : DecidablePred diagonalIndex := fun i => by unfold diagonalIndex; infer_instance

theorem source_coframe_momentum_bounds (i : Fin 6) (diagonal : diagonalIndex i) :
    43/100< sourceUnitMomentum (coframeSlot i) ∧ sourceUnitMomentum (coframeSlot i)<9/20 := by
  have select : sourceUnitMomentum (coframeSlot i)=Real.sqrt 87403953/21378 := by
    rcases diagonal with rfl|rfl|rfl <;> norm_num [sourceUnitMomentum,coframeSlot,Fin.ext_iff]
  rw [select]
  have squared:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤87403953)
  have nonnegative:=Real.sqrt_nonneg (87403953 : ℝ)
  constructor <;> nlinarith

theorem source_coframe_momentum_zero (i : Fin 6) (other : ¬diagonalIndex i) :
    sourceUnitMomentum (coframeSlot i)=0 := by
  fin_cases i <;> simp_all [diagonalIndex,sourceUnitMomentum,coframeSlot,Fin.ext_iff]

theorem off_coframe_momentum (u : FlatConfiguration)
    (box : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) (i : Fin 6) (other : ¬diagonalIndex i) :
    |u (coframeSlot i)|≤ sourceRadius := by
  simpa only [source_coframe_momentum_zero i other,sub_zero] using box (coframeSlot i)

theorem diagonal_product_bounds (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) (i : Fin 6) (diagonal : diagonalIndex i) :
    2/5≤ (fullCoordinates.symm z).1 i*u (coframeSlot i) ∧
      (fullCoordinates.symm z).1 i*u (coframeSlot i)≤1/2 := by
  have q:=abs_le.mp (coframe_box z zbox i)
  have qi : qCenter i=1 := by unfold qCenter; exact if_pos diagonal
  rw [qi] at q
  have p:=abs_le.mp (ubox (coframeSlot i))
  have p0:=source_coframe_momentum_bounds i diagonal
  have small:=radius_small.2
  have qlower : (99/100 : ℝ)≤ (fullCoordinates.symm z).1 i := by linarith
  have qupper : (fullCoordinates.symm z).1 i≤ (101/100 : ℝ) := by linarith
  have plower : (21/50 : ℝ)≤ u (coframeSlot i) := by linarith
  have pupper : u (coframeSlot i)≤ (12/25 : ℝ) := by linarith
  constructor
  · have product:=mul_le_mul qlower plower (by norm_num) (by linarith : 0≤ (fullCoordinates.symm z).1 i)
    norm_num at product
    linarith
  · have product:=mul_le_mul qupper pupper (by linarith : 0≤ u (coframeSlot i)) (by norm_num)
    norm_num at product
    linarith

def polynomialPrincipal (q : Coframe) (p : Fin 6 → ℝ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, GaussCoframeKinetic.polynomial q i j*p i*p j

def coframeTail (q : Coframe) (p : Fin 6 → ℝ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, if diagonalIndex i ∧ diagonalIndex j then 0 else
    GaussCoframeKinetic.polynomial q i j*p i*p j

theorem polynomial_principal_split (q : Coframe) (p : Fin 6 → ℝ) : polynomialPrincipal q p=
    -(q 0*p 0)^2-(q 2*p 2)^2-(q 5*p 5)^2+
      2*(q 0*p 0)*(q 2*p 2)+2*(q 0*p 0)*(q 5*p 5)+2*(q 2*p 2)*(q 5*p 5)+coframeTail q p := by
  simp [polynomialPrincipal,coframeTail,diagonalIndex,GaussCoframeKinetic.polynomial,Fin.sum_univ_succ]
  ring

theorem polynomial_entry_bound (q : Coframe) (bound : ∀ i,|q i|≤2) (i j : Fin 6) :
    |GaussCoframeKinetic.polynomial q i j|≤50 := by
  have pair (a b : Fin 6) : |q a*q b|≤4 := by
    rw [abs_mul]
    exact (mul_le_mul (bound a) (bound b) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have square (a : Fin 6) : q a^2≤4 := by simpa only [pow_two,abs_mul_self] using pair a a
  fin_cases i <;> fin_cases j <;> simp only [GaussCoframeKinetic.polynomial]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals
    first
    | (exact (pair _ _).trans (by norm_num))
    | (simpa only [abs_neg] using (pair _ _).trans (by norm_num : (4 : ℝ)≤50))
    | (rw [abs_le]; constructor <;> nlinarith [square 0,square 1,square 2,square 3,square 4,square 5,
        (abs_le.mp (pair 1 2)).1,(abs_le.mp (pair 1 2)).2,
        (abs_le.mp (pair 3 4)).1,(abs_le.mp (pair 3 4)).2])

theorem coframe_tail_bound (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1) :
    |coframeTail (fullCoordinates.symm z).1 (fun i => u (coframeSlot i))|≤1800*sourceRadius := by
  have term (i j : Fin 6) : |if diagonalIndex i ∧ diagonalIndex j then (0 : ℝ) else
      GaussCoframeKinetic.polynomial (fullCoordinates.symm z).1 i j*u (coframeSlot i)*u (coframeSlot j)|≤
      50*sourceRadius := by
    have radius:=radius_small.1
    split_ifs with diagonal
    · simp only [abs_zero]; positivity
    · have coefficient:=polynomial_entry_bound (fullCoordinates.symm z).1 (coframe_box_abs z zbox) i j
      have ui:=unit_coordinate_abs u unit (coframeSlot i)
      have uj:=unit_coordinate_abs u unit (coframeSlot j)
      rw [abs_mul,abs_mul]
      by_cases di : diagonalIndex i
      · have dj : ¬diagonalIndex j := fun h => diagonal ⟨di,h⟩
        have small:=off_coframe_momentum u ubox j dj
        have first : |GaussCoframeKinetic.polynomial (fullCoordinates.symm z).1 i j| *
            |u (coframeSlot i)|≤50 := by
          simpa using mul_le_mul coefficient ui (abs_nonneg _) (by norm_num : (0 : ℝ)≤50)
        simpa using mul_le_mul first small (abs_nonneg _) (by norm_num : (0 : ℝ)≤50)
      · have small:=off_coframe_momentum u ubox i di
        have first:=mul_le_mul coefficient small (abs_nonneg _) (by norm_num)
        have second:=mul_le_mul first uj (abs_nonneg _) (mul_nonneg (by norm_num) radius.le)
        simpa using second
  unfold coframeTail
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => term i j)))).trans (by simp; nlinarith))

theorem coframe_polynomial_positive (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i|≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1) :
    1/8< polynomialPrincipal (fullCoordinates.symm z).1 (fun i => u (coframeSlot i)) := by
  have p0:=diagonal_product_bounds z u zbox ubox 0 (by decide)
  have p2:=diagonal_product_bounds z u zbox ubox 2 (by decide)
  have p5:=diagonal_product_bounds z u zbox ubox 5 (by decide)
  have tail:=abs_le.mp (coframe_tail_bound z u zbox ubox unit)
  have small:=radius_strong
  have product02:=mul_le_mul p0.1 p2.1 (by norm_num) (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0))
  have product05:=mul_le_mul p0.1 p5.1 (by norm_num) (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0))
  have product25:=mul_le_mul p2.1 p5.1 (by norm_num) (by linarith : 0≤(fullCoordinates.symm z).1 2*u (coframeSlot 2))
  have square0:=mul_self_le_mul_self (by linarith : 0≤(fullCoordinates.symm z).1 0*u (coframeSlot 0)) p0.2
  have square2:=mul_self_le_mul_self (by linarith : 0≤(fullCoordinates.symm z).1 2*u (coframeSlot 2)) p2.2
  have square5:=mul_self_le_mul_self (by linarith : 0≤(fullCoordinates.symm z).1 5*u (coframeSlot 5)) p5.2
  rw [polynomial_principal_split]
  nlinarith

theorem A_original_numerator (z : physicalChart) (u : FlatConfiguration) :
    A z.val (nativeCovector (WithLp.toLp 2 u))=
      (polynomialPrincipal z.val.1 (fun i => u (coframeSlot i))-
        2*scalarNormSquare z.val (nativeCovector (WithLp.toLp 2 u)))/(4*volume z.val) := by
  have homogeneous : coframeQuadratic z.val (nativeCovector (WithLp.toLp 2 u))=
      sourceTime 0/(4*volume z.val)*polynomialPrincipal z.val.1 (fun i => u (coframeSlot i)) := by
    unfold coframeQuadratic
    simp_rw [native_coframe_momentum]
    unfold GaussCoframeKinetic.coefficient polynomialPrincipal
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [A,homogeneous]
  field_simp [source_time_nonzero,(volume_pos z).ne']
  ring

end LowEnergy.PreparationPhaseScalar
