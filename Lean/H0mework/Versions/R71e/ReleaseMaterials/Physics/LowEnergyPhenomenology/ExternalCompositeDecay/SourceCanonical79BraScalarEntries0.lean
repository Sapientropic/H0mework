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

theorem actual_scalar_entry_0_0 : axialInverse Complex.I 0 0 0 =
    (((1042223045172387/35669395945134500) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 0 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator0_point,actual_denominator_point]
  have hn : numeratorPoint 0 = ((24783644307598447788897600701/21083251926492057600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_0_37 : axialInverse Complex.I 0 0 37 =
    (((-28603494981963/4196399522957000) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 11 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator11_point,actual_denominator_point]
  have hn : numeratorPoint 11 = (((-3854351021054933968234856311/3904305912313344000000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_0_51 : axialInverse Complex.I 0 0 51 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 13 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator13_point,actual_denominator_point]
  have hn : numeratorPoint 13 = ((-43072206347365833771256137787/2529990231179046912000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_1_1 : axialInverse Complex.I 0 1 1 =
    (((1042223045172387/35669395945134500) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 0 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator0_point,actual_denominator_point]
  have hn : numeratorPoint 0 = ((24783644307598447788897600701/21083251926492057600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_1_36 : axialInverse Complex.I 0 1 36 =
    (((28603494981963/4196399522957000) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 27 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator27_point,actual_denominator_point]
  have hn : numeratorPoint 27 = (((3854351021054933968234856311/3904305912313344000000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_1_49 : axialInverse Complex.I 0 1 49 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 13 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator13_point,actual_denominator_point]
  have hn : numeratorPoint 13 = ((-43072206347365833771256137787/2529990231179046912000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_2_2 : axialInverse Complex.I 0 2 2 =
    (((-6225201/20798405) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 180 / denominator Complex.I 0 1) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator180_point,actual_denominator_point]
  have hn : numeratorPoint 180 = ((-48814089484558424973300643/1184595334580404224000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_2_39 : axialInverse Complex.I 0 2 39 =
    (((-534798/20798405) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 186 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator186_point,actual_denominator_point]
  have hn : numeratorPoint 186 = (((-6290321572306551200243471/493581389408501760000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_3_3 : axialInverse Complex.I 0 3 3 =
    (((-6225201/20798405) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 180 / denominator Complex.I 0 1) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator180_point,actual_denominator_point]
  have hn : numeratorPoint 180 = ((-48814089484558424973300643/1184595334580404224000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_3_38 : axialInverse Complex.I 0 3 38 =
    (((534798/20798405) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 193 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator193_point,actual_denominator_point]
  have hn : numeratorPoint 193 = (((6290321572306551200243471/493581389408501760000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_4_4 : axialInverse Complex.I 0 4 4 =
    (((-6225201/20798405) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 180 / denominator Complex.I 0 2) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator180_point,actual_denominator_point]
  have hn : numeratorPoint 180 = ((-48814089484558424973300643/1184595334580404224000000) : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_4_40 : axialInverse Complex.I 0 4 40 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 185 / denominator Complex.I 0 2) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator185_point,actual_denominator_point]
  have hn : numeratorPoint 185 = (0 : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_5_5 : axialInverse Complex.I 0 5 5 =
    (((-6225201/20798405) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 180 / denominator Complex.I 0 2) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator180_point,actual_denominator_point]
  have hn : numeratorPoint 180 = ((-48814089484558424973300643/1184595334580404224000000) : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_5_41 : axialInverse Complex.I 0 5 41 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 185 / denominator Complex.I 0 2) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator185_point,actual_denominator_point]
  have hn : numeratorPoint 185 = (0 : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_6 : axialInverse Complex.I 0 6 6 =
    (((-11828248298698869939/23449060894331420300) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 233 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator233_point,actual_denominator_point]
  have hn : numeratorPoint 233 = ((1095015857249779483096177/260287060820889600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_7 : axialInverse Complex.I 0 6 7 =
    (((33816255727616415771/117245304471657101500) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 234 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator234_point,actual_denominator_point]
  have hn : numeratorPoint 234 = ((-3130584962325059845221353/1301435304104448000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_10 : axialInverse Complex.I 0 6 10 =
    (((-27/125) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 235 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator235_point,actual_denominator_point]
  have hn : numeratorPoint 235 = ((65124842331217710284987/36150980669568000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_11 : axialInverse Complex.I 0 6 11 =
    (((-27/125) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 236 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator236_point,actual_denominator_point]
  have hn : numeratorPoint 236 = ((65124842331217710284987/36150980669568000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_43 : axialInverse Complex.I 0 6 43 =
    (((696087999675/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 242 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator242_point,actual_denominator_point]
  have hn : numeratorPoint 242 = ((-30941836048162774715/257073640316928) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_46 : axialInverse Complex.I 0 6 46 =
    (((58078125/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 243 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator243_point,actual_denominator_point]
  have hn : numeratorPoint 243 = ((-25457484016962790625/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_47 : axialInverse Complex.I 0 6 47 =
    (((255772875/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 244 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator244_point,actual_denominator_point]
  have hn : numeratorPoint 244 = ((-336340087285107175525/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_48 : axialInverse Complex.I 0 6 48 =
    (((-74169/4108750) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 245 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator245_point,actual_denominator_point]
  have hn : numeratorPoint 245 = ((54425902611455749970447/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_50 : axialInverse Complex.I 0 6 50 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 246 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator246_point,actual_denominator_point]
  have hn : numeratorPoint 246 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_53 : axialInverse Complex.I 0 6 53 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 248 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator248_point,actual_denominator_point]
  have hn : numeratorPoint 248 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_54 : axialInverse Complex.I 0 6 54 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 249 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator249_point,actual_denominator_point]
  have hn : numeratorPoint 249 = ((551178543632501108997329/156172236492533760) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_57 : axialInverse Complex.I 0 6 57 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 250 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator250_point,actual_denominator_point]
  have hn : numeratorPoint 250 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_58 : axialInverse Complex.I 0 6 58 =
    (((183076564992/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 251 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator251_point,actual_denominator_point]
  have hn : numeratorPoint 251 = ((-57342033395887339912/176518460300625) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_60 : axialInverse Complex.I 0 6 60 =
    (((589179744633/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 252 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator252_point,actual_denominator_point]
  have hn : numeratorPoint 252 = ((-94483963429912028319931/90377451673920000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_64 : axialInverse Complex.I 0 6 64 =
    (((286583257923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 253 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator253_point,actual_denominator_point]
  have hn : numeratorPoint 253 = ((-45957998909294419387961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_6_66 : axialInverse Complex.I 0 6 66 =
    (((-2150035819923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 254 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator254_point,actual_denominator_point]
  have hn : numeratorPoint 254 = ((344791055078011842321961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_6 : axialInverse Complex.I 0 7 6 =
    (((33816255727616415771/117245304471657101500) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 234 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator234_point,actual_denominator_point]
  have hn : numeratorPoint 234 = ((-3130584962325059845221353/1301435304104448000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_7 : axialInverse Complex.I 0 7 7 =
    (((-46478748610555382733/117245304471657101500) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 258 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator258_point,actual_denominator_point]
  have hn : numeratorPoint 258 = ((4302832124286978630351119/1301435304104448000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_10 : axialInverse Complex.I 0 7 10 =
    (((27/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 259 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator259_point,actual_denominator_point]
  have hn : numeratorPoint 259 = ((-65124842331217710284987/72301961339136000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_11 : axialInverse Complex.I 0 7 11 =
    (((81/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 260 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator260_point,actual_denominator_point]
  have hn : numeratorPoint 260 = ((-65124842331217710284987/24100653779712000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_42 : axialInverse Complex.I 0 7 42 =
    (((294407560425/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 265 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator265_point,actual_denominator_point]
  have hn : numeratorPoint 265 = ((-117780502224385409585/2313662762852352) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_43 : axialInverse Complex.I 0 7 43 =
    (((-696087999675/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 266 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator266_point,actual_denominator_point]
  have hn : numeratorPoint 266 = ((30941836048162774715/257073640316928) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_46 : axialInverse Complex.I 0 7 46 =
    (((-58078125/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 267 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator267_point,actual_denominator_point]
  have hn : numeratorPoint 267 = ((25457484016962790625/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_47 : axialInverse Complex.I 0 7 47 =
    (((-255772875/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 268 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator268_point,actual_denominator_point]
  have hn : numeratorPoint 268 = ((336340087285107175525/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_48 : axialInverse Complex.I 0 7 48 =
    (((74169/4108750) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 269 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator269_point,actual_denominator_point]
  have hn : numeratorPoint 269 = ((-54425902611455749970447/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_50 : axialInverse Complex.I 0 7 50 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 270 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator270_point,actual_denominator_point]
  have hn : numeratorPoint 270 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_52 : axialInverse Complex.I 0 7 52 =
    (((81/26350) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 271 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator271_point,actual_denominator_point]
  have hn : numeratorPoint 271 = (((-123576550913126584981/1338925209984000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_53 : axialInverse Complex.I 0 7 53 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 272 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator272_point,actual_denominator_point]
  have hn : numeratorPoint 272 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_54 : axialInverse Complex.I 0 7 54 =
    (((347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 273 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator273_point,actual_denominator_point]
  have hn : numeratorPoint 273 = ((-551178543632501108997329/156172236492533760) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_57 : axialInverse Complex.I 0 7 57 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 274 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator274_point,actual_denominator_point]
  have hn : numeratorPoint 274 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_58 : axialInverse Complex.I 0 7 58 =
    (((-183076564992/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 275 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator275_point,actual_denominator_point]
  have hn : numeratorPoint 275 = ((57342033395887339912/176518460300625) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_7_66 : axialInverse Complex.I 0 7 66 =
    (((2150035819923/67683863273500) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 278 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator278_point,actual_denominator_point]
  have hn : numeratorPoint 278 = ((-344791055078011842321961/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_6 : axialInverse Complex.I 0 10 6 =
    (((-27/125) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 235 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator235_point,actual_denominator_point]
  have hn : numeratorPoint 235 = ((65124842331217710284987/36150980669568000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_7 : axialInverse Complex.I 0 10 7 =
    (((27/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 259 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator259_point,actual_denominator_point]
  have hn : numeratorPoint 259 = ((-65124842331217710284987/72301961339136000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_11 : axialInverse Complex.I 0 10 11 =
    (((-27/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 283 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator283_point,actual_denominator_point]
  have hn : numeratorPoint 283 = ((65124842331217710284987/72301961339136000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_42 : axialInverse Complex.I 0 10 42 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 286 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator286_point,actual_denominator_point]
  have hn : numeratorPoint 286 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_43 : axialInverse Complex.I 0 10 43 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 287 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator287_point,actual_denominator_point]
  have hn : numeratorPoint 287 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_48 : axialInverse Complex.I 0 10 48 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_50 : axialInverse Complex.I 0 10 50 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_53 : axialInverse Complex.I 0 10 53 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_57 : axialInverse Complex.I 0 10 57 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_58 : axialInverse Complex.I 0 10 58 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 290 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator290_point,actual_denominator_point]
  have hn : numeratorPoint 290 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_60 : axialInverse Complex.I 0 10 60 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 291 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator291_point,actual_denominator_point]
  have hn : numeratorPoint 291 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_64 : axialInverse Complex.I 0 10 64 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 291 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator291_point,actual_denominator_point]
  have hn : numeratorPoint 291 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_10_66 : axialInverse Complex.I 0 10 66 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 290 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator290_point,actual_denominator_point]
  have hn : numeratorPoint 290 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_6 : axialInverse Complex.I 0 11 6 =
    (((-27/125) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 236 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator236_point,actual_denominator_point]
  have hn : numeratorPoint 236 = ((65124842331217710284987/36150980669568000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_7 : axialInverse Complex.I 0 11 7 =
    (((81/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 260 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator260_point,actual_denominator_point]
  have hn : numeratorPoint 260 = ((-65124842331217710284987/24100653779712000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_10 : axialInverse Complex.I 0 11 10 =
    (((-27/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 283 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator283_point,actual_denominator_point]
  have hn : numeratorPoint 283 = ((65124842331217710284987/72301961339136000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_11 : axialInverse Complex.I 0 11 11 =
    (((-81/250) : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 295 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator295_point,actual_denominator_point]
  have hn : numeratorPoint 295 = ((65124842331217710284987/24100653779712000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_42 : axialInverse Complex.I 0 11 42 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 298 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator298_point,actual_denominator_point]
  have hn : numeratorPoint 298 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_43 : axialInverse Complex.I 0 11 43 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 299 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator299_point,actual_denominator_point]
  have hn : numeratorPoint 299 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_46 : axialInverse Complex.I 0 11 46 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 289 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator289_point,actual_denominator_point]
  have hn : numeratorPoint 289 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_48 : axialInverse Complex.I 0 11 48 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_50 : axialInverse Complex.I 0 11 50 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_52 : axialInverse Complex.I 0 11 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_53 : axialInverse Complex.I 0 11 53 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_57 : axialInverse Complex.I 0 11 57 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_58 : axialInverse Complex.I 0 11 58 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 301 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator301_point,actual_denominator_point]
  have hn : numeratorPoint 301 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_60 : axialInverse Complex.I 0 11 60 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 302 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator302_point,actual_denominator_point]
  have hn : numeratorPoint 302 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_64 : axialInverse Complex.I 0 11 64 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 302 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator302_point,actual_denominator_point]
  have hn : numeratorPoint 302 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_11_66 : axialInverse Complex.I 0 11 66 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 301 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator301_point,actual_denominator_point]
  have hn : numeratorPoint 301 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_12_12 : axialInverse Complex.I 0 12 12 =
    (((-11177111062634090723/37518497430930272480) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 308 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator308_point,actual_denominator_point]
  have hn : numeratorPoint 308 = ((3104207878314303382408067/2892078453565440000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_12_25 : axialInverse Complex.I 0 12 25 =
    (((611673062212006469/2206970437113545440) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 311 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator311_point,actual_denominator_point]
  have hn : numeratorPoint 311 = ((-2887948914216331858691317/2892078453565440000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_12_52 : axialInverse Complex.I 0 12 52 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 318 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator318_point,actual_denominator_point]
  have hn : numeratorPoint 318 = ((43622522472333684498293/90377451673920000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_13_13 : axialInverse Complex.I 0 13 13 =
    (((152125/10393494) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 330 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator330_point,actual_denominator_point]
  have hn : numeratorPoint 330 = ((-45753776227951035571/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_13_24 : axialInverse Complex.I 0 13 24 =
    (((-15625/83147952) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 331 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator331_point,actual_denominator_point]
  have hn : numeratorPoint 331 = ((4699442915771470375/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_13_50 : axialInverse Complex.I 0 13 50 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 336 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator336_point,actual_denominator_point]
  have hn : numeratorPoint 336 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_13_53 : axialInverse Complex.I 0 13 53 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 338 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator338_point,actual_denominator_point]
  have hn : numeratorPoint 338 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_16_16 : axialInverse Complex.I 0 16 16 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 196 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator196_point,actual_denominator_point]
  have hn : numeratorPoint 196 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_16_29 : axialInverse Complex.I 0 16 29 =
    (((-2626956333/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 199 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator199_point,actual_denominator_point]
  have hn : numeratorPoint 199 = ((-7712066754541874426433689/1096847532018892800000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_17_17 : axialInverse Complex.I 0 17 17 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 196 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator196_point,actual_denominator_point]
  have hn : numeratorPoint 196 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_17_28 : axialInverse Complex.I 0 17 28 =
    (((2626956333/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 207 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator207_point,actual_denominator_point]
  have hn : numeratorPoint 207 = ((7712066754541874426433689/1096847532018892800000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_19 : axialInverse Complex.I 0 18 19 =
    (((1254786105956609/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 34 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator34_point,actual_denominator_point]
  have hn : numeratorPoint 34 = ((89514924879639556283603337821/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_23 : axialInverse Complex.I 0 18 23 =
    (((-2909121625/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 36 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator36_point,actual_denominator_point]
  have hn : numeratorPoint 36 = ((-35873362654763350980117359/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
