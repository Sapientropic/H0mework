import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

theorem actual_scalar_entry_63_19 : axialInverse Complex.I 0 63 19 =
    (((-180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 66 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator66_point,actual_denominator_point]
  have hn : numeratorPoint 66 = ((-2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_22 : axialInverse Complex.I 0 63 22 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 78 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator78_point,actual_denominator_point]
  have hn : numeratorPoint 78 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_30 : axialInverse Complex.I 0 63 30 =
    (((-227249457845/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 161 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator161_point,actual_denominator_point]
  have hn : numeratorPoint 161 = (((-1708713367652148228219566147/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_31 : axialInverse Complex.I 0 63 31 =
    (((269002064095/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 162 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator162_point,actual_denominator_point]
  have hn : numeratorPoint 162 = (((2022655751102641216301029897/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_34 : axialInverse Complex.I 0 63 34 =
    (((483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 163 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator163_point,actual_denominator_point]
  have hn : numeratorPoint 163 = (((636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_35 : axialInverse Complex.I 0 63 35 =
    (((2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 164 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator164_point,actual_denominator_point]
  have hn : numeratorPoint 164 = (((1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_55 : axialInverse Complex.I 0 63 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_56 : axialInverse Complex.I 0 63 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 150 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator150_point,actual_denominator_point]
  have hn : numeratorPoint 150 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_61 : axialInverse Complex.I 0 63 61 =
    (((45/82) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 155 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator155_point,actual_denominator_point]
  have hn : numeratorPoint 155 = ((124127395813734391271631521/6507176520522240000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_63 : axialInverse Complex.I 0 63 63 =
    (((300597087565/1082941812376) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 166 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator166_point,actual_denominator_point]
  have hn : numeratorPoint 166 = ((2260222165854200959748285419/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_67 : axialInverse Complex.I 0 63 67 =
    (((-7163420695/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 167 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator167_point,actual_denominator_point]
  have hn : numeratorPoint 167 = ((-2208364083440237126030449337/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_6 : axialInverse Complex.I 0 64 6 =
    (((286583257923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 253 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator253_point,actual_denominator_point]
  have hn : numeratorPoint 253 = ((-45957998909294419387961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_10 : axialInverse Complex.I 0 64 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 291 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator291_point,actual_denominator_point]
  have hn : numeratorPoint 291 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_11 : axialInverse Complex.I 0 64 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 302 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator302_point,actual_denominator_point]
  have hn : numeratorPoint 302 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_42 : axialInverse Complex.I 0 64 42 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 387 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator387_point,actual_denominator_point]
  have hn : numeratorPoint 387 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_46 : axialInverse Complex.I 0 64 46 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 413 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator413_point,actual_denominator_point]
  have hn : numeratorPoint 413 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_47 : axialInverse Complex.I 0 64 47 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 419 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator419_point,actual_denominator_point]
  have hn : numeratorPoint 419 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_48 : axialInverse Complex.I 0 64 48 =
    (((3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 429 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator429_point,actual_denominator_point]
  have hn : numeratorPoint 429 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_50 : axialInverse Complex.I 0 64 50 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 441 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator441_point,actual_denominator_point]
  have hn : numeratorPoint 441 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_53 : axialInverse Complex.I 0 64 53 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 441 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator441_point,actual_denominator_point]
  have hn : numeratorPoint 441 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_54 : axialInverse Complex.I 0 64 54 =
    (((71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 452 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator452_point,actual_denominator_point]
  have hn : numeratorPoint 452 = ((-112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_64_57 : axialInverse Complex.I 0 64 57 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 458 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator458_point,actual_denominator_point]
  have hn : numeratorPoint 458 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_6 : axialInverse Complex.I 0 66 6 =
    (((-2150035819923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 254 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator254_point,actual_denominator_point]
  have hn : numeratorPoint 254 = ((344791055078011842321961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_7 : axialInverse Complex.I 0 66 7 =
    (((2150035819923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 278 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator278_point,actual_denominator_point]
  have hn : numeratorPoint 278 = ((-344791055078011842321961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_10 : axialInverse Complex.I 0 66 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 290 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator290_point,actual_denominator_point]
  have hn : numeratorPoint 290 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_11 : axialInverse Complex.I 0 66 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 301 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator301_point,actual_denominator_point]
  have hn : numeratorPoint 301 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_42 : axialInverse Complex.I 0 66 42 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 388 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator388_point,actual_denominator_point]
  have hn : numeratorPoint 388 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_43 : axialInverse Complex.I 0 66 43 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 406 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator406_point,actual_denominator_point]
  have hn : numeratorPoint 406 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_46 : axialInverse Complex.I 0 66 46 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 412 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator412_point,actual_denominator_point]
  have hn : numeratorPoint 412 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_47 : axialInverse Complex.I 0 66 47 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 418 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator418_point,actual_denominator_point]
  have hn : numeratorPoint 418 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_48 : axialInverse Complex.I 0 66 48 =
    (((-3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 430 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator430_point,actual_denominator_point]
  have hn : numeratorPoint 430 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_50 : axialInverse Complex.I 0 66 50 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 442 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator442_point,actual_denominator_point]
  have hn : numeratorPoint 442 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_52 : axialInverse Complex.I 0 66 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_53 : axialInverse Complex.I 0 66 53 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 442 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator442_point,actual_denominator_point]
  have hn : numeratorPoint 442 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_54 : axialInverse Complex.I 0 66 54 =
    (((71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 453 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator453_point,actual_denominator_point]
  have hn : numeratorPoint 453 = ((-112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_57 : axialInverse Complex.I 0 66 57 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 459 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator459_point,actual_denominator_point]
  have hn : numeratorPoint 459 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_58 : axialInverse Complex.I 0 66 58 =
    (((-1324754695809/10829418123760) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 464 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator464_point,actual_denominator_point]
  have hn : numeratorPoint 464 = ((70814877447622241572721/80335512599040000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_66_66 : axialInverse Complex.I 0 66 66 =
    (((834525625209/10829418123760) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 461 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator461_point,actual_denominator_point]
  have hn : numeratorPoint 461 = ((-133828919564583539723963/241006537797120000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_18 : axialInverse Complex.I 0 67 18 =
    (((-6343882959/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 49 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator49_point,actual_denominator_point]
  have hn : numeratorPoint 49 = ((-3259523597430378755370051799/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_19 : axialInverse Complex.I 0 67 19 =
    (((5121855459/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 67 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator67_point,actual_denominator_point]
  have hn : numeratorPoint 67 = ((877212943509797593069041433/260287060820889600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_22 : axialInverse Complex.I 0 67 22 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 79 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator79_point,actual_denominator_point]
  have hn : numeratorPoint 79 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_30 : axialInverse Complex.I 0 67 30 =
    (((2900539445/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 52 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator52_point,actual_denominator_point]
  have hn : numeratorPoint 52 = (((894188322264895135298870587/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_31 : axialInverse Complex.I 0 67 31 =
    (((-1882183195/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 70 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator70_point,actual_denominator_point]
  have hn : numeratorPoint 70 = (((-580245938814402147217406837/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_34 : axialInverse Complex.I 0 67 34 =
    (((483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 82 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator82_point,actual_denominator_point]
  have hn : numeratorPoint 82 = (((636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_35 : axialInverse Complex.I 0 67 35 =
    (((2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 92 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator92_point,actual_denominator_point]
  have hn : numeratorPoint 92 = (((1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_55 : axialInverse Complex.I 0 67 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_56 : axialInverse Complex.I 0 67 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_61 : axialInverse Complex.I 0 67 61 =
    (((-298920165/3301651867) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 156 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator156_point,actual_denominator_point]
  have hn : numeratorPoint 156 = ((-30717380439152026719089113/9760764780783360000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_63 : axialInverse Complex.I 0 67 63 =
    (((-7163420695/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 167 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator167_point,actual_denominator_point]
  have hn : numeratorPoint 167 = ((-2208364083440237126030449337/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_67_67 : axialInverse Complex.I 0 67 67 =
    (((-9554782015/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 171 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator171_point,actual_denominator_point]
  have hn : numeratorPoint 171 = ((-2945581213979885767288588049/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_18 : axialInverse Complex.I 0 71 18 =
    (((124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 98 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator98_point,actual_denominator_point]
  have hn : numeratorPoint 98 = (((310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_19 : axialInverse Complex.I 0 71 19 =
    (((-124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 105 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator105_point,actual_denominator_point]
  have hn : numeratorPoint 105 = (((-310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_22 : axialInverse Complex.I 0 71 22 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 111 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator111_point,actual_denominator_point]
  have hn : numeratorPoint 111 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_23 : axialInverse Complex.I 0 71 23 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 116 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator116_point,actual_denominator_point]
  have hn : numeratorPoint 116 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_30 : axialInverse Complex.I 0 71 30 =
    (((136349674707/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 47 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator47_point,actual_denominator_point]
  have hn : numeratorPoint 47 = ((1708713367652148228219566147/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_31 : axialInverse Complex.I 0 71 31 =
    (((-161401238457/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 65 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator65_point,actual_denominator_point]
  have hn : numeratorPoint 65 = ((-2022655751102641216301029897/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_34 : axialInverse Complex.I 0 71 34 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 77 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator77_point,actual_denominator_point]
  have hn : numeratorPoint 77 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_55 : axialInverse Complex.I 0 71 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 151 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator151_point,actual_denominator_point]
  have hn : numeratorPoint 151 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_56 : axialInverse Complex.I 0 71 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_71 : axialInverse Complex.I 0 71 71 =
    (((124062880485/270735453094) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 154 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator154_point,actual_denominator_point]
  have hn : numeratorPoint 154 = ((310947426562899120376716337/19521529561566720000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_73 : axialInverse Complex.I 0 71 73 =
    (((-45/82) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 176 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator176_point,actual_denominator_point]
  have hn : numeratorPoint 176 = ((-124127395813734391271631521/6507176520522240000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_71_77 : axialInverse Complex.I 0 71 77 =
    (((-298920165/3301651867) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 156 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator156_point,actual_denominator_point]
  have hn : numeratorPoint 156 = ((-30717380439152026719089113/9760764780783360000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_18 : axialInverse Complex.I 0 73 18 =
    (((-227249457845/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 161 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator161_point,actual_denominator_point]
  have hn : numeratorPoint 161 = (((-1708713367652148228219566147/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_19 : axialInverse Complex.I 0 73 19 =
    (((269002064095/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 162 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator162_point,actual_denominator_point]
  have hn : numeratorPoint 162 = (((2022655751102641216301029897/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_22 : axialInverse Complex.I 0 73 22 =
    (((483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 163 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator163_point,actual_denominator_point]
  have hn : numeratorPoint 163 = (((636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_23 : axialInverse Complex.I 0 73 23 =
    (((2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 164 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator164_point,actual_denominator_point]
  have hn : numeratorPoint 164 = (((1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_30 : axialInverse Complex.I 0 73 30 =
    (((-180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 100 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator100_point,actual_denominator_point]
  have hn : numeratorPoint 100 = ((-2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_31 : axialInverse Complex.I 0 73 31 =
    (((180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 107 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator107_point,actual_denominator_point]
  have hn : numeratorPoint 107 = ((2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_34 : axialInverse Complex.I 0 73 34 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 113 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator113_point,actual_denominator_point]
  have hn : numeratorPoint 113 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_55 : axialInverse Complex.I 0 73 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 150 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator150_point,actual_denominator_point]
  have hn : numeratorPoint 150 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_56 : axialInverse Complex.I 0 73 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 153 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator153_point,actual_denominator_point]
  have hn : numeratorPoint 153 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_71 : axialInverse Complex.I 0 73 71 =
    (((-45/82) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 176 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator176_point,actual_denominator_point]
  have hn : numeratorPoint 176 = ((-124127395813734391271631521/6507176520522240000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_73 : axialInverse Complex.I 0 73 73 =
    (((300597087565/1082941812376) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 166 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator166_point,actual_denominator_point]
  have hn : numeratorPoint 166 = ((2260222165854200959748285419/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_73_77 : axialInverse Complex.I 0 73 77 =
    (((7163420695/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 178 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator178_point,actual_denominator_point]
  have hn : numeratorPoint 178 = ((2208364083440237126030449337/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_18 : axialInverse Complex.I 0 77 18 =
    (((-2900539445/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 99 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator99_point,actual_denominator_point]
  have hn : numeratorPoint 99 = (((-894188322264895135298870587/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_19 : axialInverse Complex.I 0 77 19 =
    (((1882183195/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 106 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator106_point,actual_denominator_point]
  have hn : numeratorPoint 106 = (((580245938814402147217406837/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_22 : axialInverse Complex.I 0 77 22 =
    (((-483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 112 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator112_point,actual_denominator_point]
  have hn : numeratorPoint 112 = (((-636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_23 : axialInverse Complex.I 0 77 23 =
    (((-2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 117 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator117_point,actual_denominator_point]
  have hn : numeratorPoint 117 = (((-1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_30 : axialInverse Complex.I 0 77 30 =
    (((-6343882959/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 49 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator49_point,actual_denominator_point]
  have hn : numeratorPoint 49 = ((-3259523597430378755370051799/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_31 : axialInverse Complex.I 0 77 31 =
    (((5121855459/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 67 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator67_point,actual_denominator_point]
  have hn : numeratorPoint 67 = ((877212943509797593069041433/260287060820889600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_34 : axialInverse Complex.I 0 77 34 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 79 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator79_point,actual_denominator_point]
  have hn : numeratorPoint 79 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_55 : axialInverse Complex.I 0 77 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_56 : axialInverse Complex.I 0 77 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_71 : axialInverse Complex.I 0 77 71 =
    (((-298920165/3301651867) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 156 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator156_point,actual_denominator_point]
  have hn : numeratorPoint 156 = ((-30717380439152026719089113/9760764780783360000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_73 : axialInverse Complex.I 0 77 73 =
    (((7163420695/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 178 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator178_point,actual_denominator_point]
  have hn : numeratorPoint 178 = ((2208364083440237126030449337/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_77_77 : axialInverse Complex.I 0 77 77 =
    (((-9554782015/26413214936) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 171 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator171_point,actual_denominator_point]
  have hn : numeratorPoint 171 = ((-2945581213979885767288588049/234258354738800640000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
