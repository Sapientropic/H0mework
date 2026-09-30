import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Sum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedQuinticWeights NativeUnheatedTriadSum
noncomputable section

def middleIndex (wave : IntegerWavevector) : Index ≃ Index where
  toFun index := ((index.1.1, wave-index.1.1-index.1.2), index.2)
  invFun index := ((index.1.1, wave-index.1.1-index.1.2), index.2)
  left_inv := by rintro ⟨⟨c,a⟩,d⟩; simp only [sub_sub_cancel]
  right_inv := by rintro ⟨⟨c,a⟩,d⟩; simp only [sub_sub_cancel]

def outerIndex (wave : IntegerWavevector) : Index ≃ Index where
  toFun index := ((wave-index.1.1-index.1.2,index.1.1),index.2)
  invFun index := ((index.1.2,wave-index.1.1-index.1.2),index.2)
  left_inv := by
    rintro ⟨⟨c,a⟩,d⟩
    change ((c,wave-(wave-c-a)-c),d) = ((c,a),d)
    rw [show wave-(wave-c-a)-c = a by abel]
  right_inv := by
    rintro ⟨⟨c,a⟩,d⟩
    change ((wave-a-(wave-c-a),a),d) = ((c,a),d)
    rw [show wave-a-(wave-c-a) = c by abel]

def middleTerm (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate)
    (L R U V : E) (index : Index) : ℂ :=
  kernel index*(L index.2 i*R ((wave-index.1.1-index.1.2)-index.2) j*U index.1.2 l*V index.1.1 m)

def outerTerm (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate)
    (L R U V : E) (index : Index) : ℂ :=
  kernel index*(L index.1.2 i*R (wave-index.1.1-index.1.2) j*U index.2 l*V (index.1.1-index.2) m)

theorem middle_reindex (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate)
    (L R U V : E) (index : Index) :
    middleTerm kernel wave i j l m L R U V index =
      term (fun index => kernel ((middleIndex wave).symm index)) wave i j l m L R U V (middleIndex wave index) := by
  rcases index with ⟨⟨c,a⟩,d⟩
  simp only [middleTerm, term, middleIndex, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, sub_sub_cancel]

theorem outer_reindex (kernel : Index → ℂ) (wave : IntegerWavevector) (i j l m : Coordinate)
    (L R U V : E) (index : Index) :
    outerTerm kernel wave i j l m L R U V index =
      term (fun index => kernel ((outerIndex wave).symm index)) wave l m i j U V L R (outerIndex wave index) := by
  rcases index with ⟨⟨c,a⟩,d⟩
  have same : wave-(wave-c-a)-c = a := by abel
  simp only [outerTerm, term, outerIndex, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, same]
  ring

theorem middle_kernel (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta index.1.1) :
    ∀ index, ‖kernel ((middleIndex wave).symm index)‖ ≤ cap*eta (wave-index.1.1-index.1.2)*eta index.1.1 := by
  intro index
  exact bounded ((middleIndex wave).symm index)

theorem outer_kernel (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta (wave-index.1.1-index.1.2)) :
    ∀ index, ‖kernel ((outerIndex wave).symm index)‖ ≤ cap*eta (wave-index.1.1-index.1.2)*eta index.1.1 := by
  rintro ⟨⟨c,a⟩,d⟩
  have same : wave-a-(wave-c-a) = c := by abel
  simpa only [outerIndex, Equiv.coe_fn_symm_mk, same] using bounded ((outerIndex wave).symm ((c,a),d))

theorem middle_absolute_summable (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta index.1.1)
    (i j l m : Coordinate) (L R U V : E) :
    Summable (fun index => ‖middleTerm kernel wave i j l m L R U V index‖) := by
  have generated := absolute_summable _ cap wave (middle_kernel kernel cap wave bounded) i j l m L R U V
  have moved := (middleIndex wave).summable_iff.mpr generated
  exact moved.congr fun index => (congrArg norm (middle_reindex kernel wave i j l m L R U V index)).symm

theorem middle_absolute_bound (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta index.1.1)
    (i j l m : Coordinate) (L R U V : E) :
    (∑' index, ‖middleTerm kernel wave i j l m L R U V index‖) ≤ (3*cap*‖etaL2‖^2)*‖L‖*‖R‖*‖U‖*‖V‖ := by
  simp_rw [middle_reindex]
  rw [(middleIndex wave).tsum_eq (fun index =>
    ‖term (fun index => kernel ((middleIndex wave).symm index)) wave i j l m L R U V index‖)]
  exact absolute_bound _ cap wave (middle_kernel kernel cap wave bounded) i j l m L R U V

theorem outer_absolute_summable (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta (wave-index.1.1-index.1.2))
    (i j l m : Coordinate) (L R U V : E) :
    Summable (fun index => ‖outerTerm kernel wave i j l m L R U V index‖) := by
  have generated := absolute_summable _ cap wave (outer_kernel kernel cap wave bounded) l m i j U V L R
  have moved := (outerIndex wave).summable_iff.mpr generated
  exact moved.congr fun index => (congrArg norm (outer_reindex kernel wave i j l m L R U V index)).symm

theorem outer_absolute_bound (kernel : Index → ℂ) (cap : ℝ) (wave : IntegerWavevector)
    (bounded : ∀ index, ‖kernel index‖ ≤ cap*eta index.1.2*eta (wave-index.1.1-index.1.2))
    (i j l m : Coordinate) (L R U V : E) :
    (∑' index, ‖outerTerm kernel wave i j l m L R U V index‖) ≤ (3*cap*‖etaL2‖^2)*‖L‖*‖R‖*‖U‖*‖V‖ := by
  simp_rw [outer_reindex]
  rw [(outerIndex wave).tsum_eq (fun index =>
    ‖term (fun index => kernel ((outerIndex wave).symm index)) wave l m i j U V L R index‖)]
  exact (absolute_bound _ cap wave (outer_kernel kernel cap wave bounded) l m i j U V L R).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticSum
