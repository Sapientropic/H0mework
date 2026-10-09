import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B182
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B183

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4385_pa : Scalar.QComplex := ((999997936089834535201026591790 : Int)/10^30,(-2031702751685006415196144448 : Int)/10^30)
theorem v4385_pa_checked : Scalar.distance (sourceCoefficient 70 81 1 0) v4385_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4385_pb : Scalar.QComplex := ((-876634063028312355599818 : Int)/10^30,(-431476628659048372828629126 : Int)/10^30)
theorem v4385_pb_checked : Scalar.distance (sourceCoefficient 70 81 1 1) v4385_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4385_pg : Scalar.QComplex := ((-93086237579621278947151 : Int)/10^30,(189123955369374823647 : Int)/10^30)
theorem v4385_pg_checked : Scalar.distance (sourceCoefficient 70 81 1 2) v4385_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4385_mb : Scalar.QComplex := ((-1248978634164176824691709 : Int)/10^30,(-431475711504865806093884451 : Int)/10^30)
theorem v4385_mb_checked : Scalar.distance (sourceCoefficient 70 81 3 1) v4385_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4385_mg : Scalar.QComplex := ((-93086039713905119815258 : Int)/10^30,(269453115532586429640 : Int)/10^30)
theorem v4385_mg_checked : Scalar.distance (sourceCoefficient 70 81 3 2) v4385_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4385_upper : Scalar.QComplex := ((999992940175741964168074220544 : Int)/10^30,(-3757605444289369439753560323 : Int)/10^30)
theorem v4385_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 81 5) 1) 14) v4385_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4385 : Material (70 : Basis) (81 : Basis) where
  plus := ![v4385_pa,v4385_pb,v4385_pg]
  minus := ![(Primitive.Addresses.material4385 1).one,v4385_mb,v4385_mg]
  upper := v4385_upper
  lower := (Primitive.Addresses.material4385 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4385_pa_checked.trans (by decide +kernel)
    · exact v4385_pb_checked.trans (by decide +kernel)
    · exact v4385_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 81 Primitive.Addresses.material4385
    · exact v4385_mb_checked.trans (by decide +kernel)
    · exact v4385_mg_checked.trans (by decide +kernel)
  upper_error := v4385_upper_checked
  lower_error := reuse_lower_error 70 81 Primitive.Addresses.material4385

def v4386_pa : Scalar.QComplex := ((999997915844778895959508646233 : Int)/10^30,(-2041642989972805046457923389 : Int)/10^30)
theorem v4386_pa_checked : Scalar.distance (sourceCoefficient 70 82 1 0) v4386_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4386_pb : Scalar.QComplex := ((-880923051907209032346986 : Int)/10^30,(-431476619689794539278663423 : Int)/10^30)
theorem v4386_pb_checked : Scalar.distance (sourceCoefficient 70 82 1 1) v4386_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4386_pg : Scalar.QComplex := ((-93086235669843405535850 : Int)/10^30,(190049256610442699051 : Int)/10^30)
theorem v4386_pg_checked : Scalar.distance (sourceCoefficient 70 82 1 2) v4386_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4386_mb : Scalar.QComplex := ((-1253267613706024827193803 : Int)/10^30,(-431475698834411078607543403 : Int)/10^30)
theorem v4386_mb_checked : Scalar.distance (sourceCoefficient 70 82 3 1) v4386_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4386_mg : Scalar.QComplex := ((-93086037005634660480849 : Int)/10^30,(270378414781070073087 : Int)/10^30)
theorem v4386_mg_checked : Scalar.distance (sourceCoefficient 70 82 3 2) v4386_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4386_upper : Scalar.QComplex := ((999992902774766964191559777430 : Int)/10^30,(-3767545632831221387522240205 : Int)/10^30)
theorem v4386_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 82 5) 1) 14) v4386_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4386 : Material (70 : Basis) (82 : Basis) where
  plus := ![v4386_pa,v4386_pb,v4386_pg]
  minus := ![(Primitive.Addresses.material4386 1).one,v4386_mb,v4386_mg]
  upper := v4386_upper
  lower := (Primitive.Addresses.material4386 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4386_pa_checked.trans (by decide +kernel)
    · exact v4386_pb_checked.trans (by decide +kernel)
    · exact v4386_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 82 Primitive.Addresses.material4386
    · exact v4386_mb_checked.trans (by decide +kernel)
    · exact v4386_mg_checked.trans (by decide +kernel)
  upper_error := v4386_upper_checked
  lower_error := reuse_lower_error 70 82 Primitive.Addresses.material4386

def v4387_pa : Scalar.QComplex := ((999997888050445775010531735712 : Int)/10^30,(-2055211582324082598832837886 : Int)/10^30)
theorem v4387_pa_checked : Scalar.distance (sourceCoefficient 70 83 1 0) v4387_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4387_pb : Scalar.QComplex := ((-886777593767144730213325 : Int)/10^30,(-431476607354856185671337323 : Int)/10^30)
theorem v4387_pb_checked : Scalar.distance (sourceCoefficient 70 83 1 1) v4387_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4387_pg : Scalar.QComplex := ((-93086233045643567487200 : Int)/10^30,(191312308352269765194 : Int)/10^30)
theorem v4387_pg_checked : Scalar.distance (sourceCoefficient 70 83 1 2) v4387_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4387_mb : Scalar.QComplex := ((-1259122142741550770662589 : Int)/10^30,(-431475681447271371514148822 : Int)/10^30)
theorem v4387_mb_checked : Scalar.distance (sourceCoefficient 70 83 3 1) v4387_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4387_mg : Scalar.QComplex := ((-93086033291479032083726 : Int)/10^30,(271641463788038980769 : Int)/10^30)
theorem v4387_mg_checked : Scalar.distance (sourceCoefficient 70 83 3 2) v4387_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4387_upper : Scalar.QComplex := ((999992851562315774414345745313 : Int)/10^30,(-3781114157003177026936762323 : Int)/10^30)
theorem v4387_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 83 5) 1) 14) v4387_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4387 : Material (70 : Basis) (83 : Basis) where
  plus := ![v4387_pa,v4387_pb,v4387_pg]
  minus := ![(Primitive.Addresses.material4387 1).one,v4387_mb,v4387_mg]
  upper := v4387_upper
  lower := (Primitive.Addresses.material4387 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4387_pa_checked.trans (by decide +kernel)
    · exact v4387_pb_checked.trans (by decide +kernel)
    · exact v4387_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 83 Primitive.Addresses.material4387
    · exact v4387_mb_checked.trans (by decide +kernel)
    · exact v4387_mg_checked.trans (by decide +kernel)
  upper_error := v4387_upper_checked
  lower_error := reuse_lower_error 70 83 Primitive.Addresses.material4387

def v4388_pa : Scalar.QComplex := ((999997815214873102196043767680 : Int)/10^30,(-2090350564022589297756372362 : Int)/10^30)
theorem v4388_pa_checked : Scalar.distance (sourceCoefficient 70 84 1 0) v4388_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4388_pb : Scalar.QComplex := ((-901939272286669903691944 : Int)/10^30,(-431476574918376080540121568 : Int)/10^30)
theorem v4388_pb_checked : Scalar.distance (sourceCoefficient 70 84 1 1) v4388_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4388_pg : Scalar.QComplex := ((-93086226156738684260471 : Int)/10^30,(194583270472108284119 : Int)/10^30)
theorem v4388_pg_checked : Scalar.distance (sourceCoefficient 70 84 1 2) v4388_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4388_mb : Scalar.QComplex := ((-1274283787624468662487658 : Int)/10^30,(-431475635926957638268360839 : Int)/10^30)
theorem v4388_mb_checked : Scalar.distance (sourceCoefficient 70 84 3 1) v4388_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4388_mg : Scalar.QComplex := ((-93086023579883723155634 : Int)/10^30,(274912418745134162658 : Int)/10^30)
theorem v4388_mg_checked : Scalar.distance (sourceCoefficient 70 84 3 2) v4388_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4388_upper : Scalar.QComplex := ((999992718080156953525014453446 : Int)/10^30,(-3816252960658707358940420642 : Int)/10^30)
theorem v4388_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 84 5) 1) 14) v4388_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4388 : Material (70 : Basis) (84 : Basis) where
  plus := ![v4388_pa,v4388_pb,v4388_pg]
  minus := ![(Primitive.Addresses.material4388 1).one,v4388_mb,v4388_mg]
  upper := v4388_upper
  lower := (Primitive.Addresses.material4388 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4388_pa_checked.trans (by decide +kernel)
    · exact v4388_pb_checked.trans (by decide +kernel)
    · exact v4388_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 84 Primitive.Addresses.material4388
    · exact v4388_mb_checked.trans (by decide +kernel)
    · exact v4388_mg_checked.trans (by decide +kernel)
  upper_error := v4388_upper_checked
  lower_error := reuse_lower_error 70 84 Primitive.Addresses.material4388

def v4389_pa : Scalar.QComplex := ((999997646833426973582339158434 : Int)/10^30,(-2169407202131475111782910948 : Int)/10^30)
theorem v4389_pa_checked : Scalar.distance (sourceCoefficient 70 85 1 0) v4389_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4389_pb : Scalar.QComplex := ((-936050427912072908918094 : Int)/10^30,(-431476499344988741385489792 : Int)/10^30)
theorem v4389_pb_checked : Scalar.distance (sourceCoefficient 70 85 1 1) v4389_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4389_pg : Scalar.QComplex := ((-93086210167670010879523 : Int)/10^30,(201942369960902138778 : Int)/10^30)
theorem v4389_pg_checked : Scalar.distance (sourceCoefficient 70 85 1 2) v4389_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4389_mb : Scalar.QComplex := ((-1308394865332299896874220 : Int)/10^30,(-431475530917207443235798128 : Int)/10^30)
theorem v4389_mb_checked : Scalar.distance (sourceCoefficient 70 85 3 1) v4389_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4389_mg : Scalar.QComplex := ((-93086001240249585943880 : Int)/10^30,(282271501695952805970 : Int)/10^30)
theorem v4389_mg_checked : Scalar.distance (sourceCoefficient 70 85 3 2) v4389_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4389_upper : Scalar.QComplex := ((999992413254376195543873365359 : Int)/10^30,(-3895309190410916782325346534 : Int)/10^30)
theorem v4389_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 85 5) 1) 14) v4389_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4389 : Material (70 : Basis) (85 : Basis) where
  plus := ![v4389_pa,v4389_pb,v4389_pg]
  minus := ![(Primitive.Addresses.material4389 1).one,v4389_mb,v4389_mg]
  upper := v4389_upper
  lower := (Primitive.Addresses.material4389 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4389_pa_checked.trans (by decide +kernel)
    · exact v4389_pb_checked.trans (by decide +kernel)
    · exact v4389_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 85 Primitive.Addresses.material4389
    · exact v4389_mb_checked.trans (by decide +kernel)
    · exact v4389_mg_checked.trans (by decide +kernel)
  upper_error := v4389_upper_checked
  lower_error := reuse_lower_error 70 85 Primitive.Addresses.material4389

def v4390_pa : Scalar.QComplex := ((999997615087039350838413743877 : Int)/10^30,(-2183991811680733683094264630 : Int)/10^30)
theorem v4390_pa_checked : Scalar.distance (sourceCoefficient 70 86 1 0) v4390_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4390_pb : Scalar.QComplex := ((-942343357601786407238387 : Int)/10^30,(-431476485010125756502136390 : Int)/10^30)
theorem v4390_pb_checked : Scalar.distance (sourceCoefficient 70 86 1 1) v4390_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4390_pg : Scalar.QComplex := ((-93086207143798210224603 : Int)/10^30,(203299999035274506389 : Int)/10^30)
theorem v4390_pg_checked : Scalar.distance (sourceCoefficient 70 86 1 2) v4390_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4390_mb : Scalar.QComplex := ((-1314687780308526932927604 : Int)/10^30,(-431475511151834896686387745 : Int)/10^30)
theorem v4390_mb_checked : Scalar.distance (sourceCoefficient 70 86 3 1) v4390_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4390_mg : Scalar.QComplex := ((-93085997044806165374964 : Int)/10^30,(283629127655352648644 : Int)/10^30)
theorem v4390_mg_checked : Scalar.distance (sourceCoefficient 70 86 3 2) v4390_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4390_upper : Scalar.QComplex := ((999992356336322878737601508838 : Int)/10^30,(-3909893723446727631533176562 : Int)/10^30)
theorem v4390_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 86 5) 1) 14) v4390_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4390 : Material (70 : Basis) (86 : Basis) where
  plus := ![v4390_pa,v4390_pb,v4390_pg]
  minus := ![(Primitive.Addresses.material4390 1).one,v4390_mb,v4390_mg]
  upper := v4390_upper
  lower := (Primitive.Addresses.material4390 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4390_pa_checked.trans (by decide +kernel)
    · exact v4390_pb_checked.trans (by decide +kernel)
    · exact v4390_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 86 Primitive.Addresses.material4390
    · exact v4390_mb_checked.trans (by decide +kernel)
    · exact v4390_mg_checked.trans (by decide +kernel)
  upper_error := v4390_upper_checked
  lower_error := reuse_lower_error 70 86 Primitive.Addresses.material4390

def v4391_pa : Scalar.QComplex := ((999997612977368851253967429425 : Int)/10^30,(-2184957565816885709904254964 : Int)/10^30)
theorem v4391_pa_checked : Scalar.distance (sourceCoefficient 70 87 1 0) v4391_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4391_pb : Scalar.QComplex := ((-942760058701109399254436 : Int)/10^30,(-431476484056589246665968266 : Int)/10^30)
theorem v4391_pb_checked : Scalar.distance (sourceCoefficient 70 87 1 1) v4391_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4391_pg : Scalar.QComplex := ((-93086206942749965571065 : Int)/10^30,(203389897629046438979 : Int)/10^30)
theorem v4391_pg_checked : Scalar.distance (sourceCoefficient 70 87 1 2) v4391_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4391_mb : Scalar.QComplex := ((-1315104480429833999186234 : Int)/10^30,(-431475509838704460700529280 : Int)/10^30)
theorem v4391_mb_checked : Scalar.distance (sourceCoefficient 70 87 3 1) v4391_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4391_mg : Scalar.QComplex := ((-93085996766179558038060 : Int)/10^30,(283719026042155645945 : Int)/10^30)
theorem v4391_mg_checked : Scalar.distance (sourceCoefficient 70 87 3 2) v4391_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4391_upper : Scalar.QComplex := ((999992352559851494791986925392 : Int)/10^30,(-3910859472503402423524592005 : Int)/10^30)
theorem v4391_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 87 5) 1) 14) v4391_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4391 : Material (70 : Basis) (87 : Basis) where
  plus := ![v4391_pa,v4391_pb,v4391_pg]
  minus := ![(Primitive.Addresses.material4391 1).one,v4391_mb,v4391_mg]
  upper := v4391_upper
  lower := (Primitive.Addresses.material4391 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4391_pa_checked.trans (by decide +kernel)
    · exact v4391_pb_checked.trans (by decide +kernel)
    · exact v4391_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 87 Primitive.Addresses.material4391
    · exact v4391_mb_checked.trans (by decide +kernel)
    · exact v4391_mg_checked.trans (by decide +kernel)
  upper_error := v4391_upper_checked
  lower_error := reuse_lower_error 70 87 Primitive.Addresses.material4391

def v4392_pa : Scalar.QComplex := ((999997587214012086704131634911 : Int)/10^30,(-2196717131150564926096620701 : Int)/10^30)
theorem v4392_pa_checked : Scalar.distance (sourceCoefficient 70 88 1 0) v4392_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4392_pb : Scalar.QComplex := ((-947834045536232089194224 : Int)/10^30,(-431476472402746937480349825 : Int)/10^30)
theorem v4392_pb_checked : Scalar.distance (sourceCoefficient 70 88 1 1) v4392_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4392_pg : Scalar.QComplex := ((-93086204486547708294370 : Int)/10^30,(204484553446849228623 : Int)/10^30)
theorem v4392_pg_checked : Scalar.distance (sourceCoefficient 70 88 1 2) v4392_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4392_mb : Scalar.QComplex := ((-1320178455318938454502092 : Int)/10^30,(-431475493806244375945976637 : Int)/10^30)
theorem v4392_mb_checked : Scalar.distance (sourceCoefficient 70 88 3 1) v4392_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4392_mg : Scalar.QComplex := ((-93085993365339546021789 : Int)/10^30,(284813679332776121592 : Int)/10^30)
theorem v4392_mg_checked : Scalar.distance (sourceCoefficient 70 88 3 2) v4392_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4392_upper : Scalar.QComplex := ((999992306500590155238883597688 : Int)/10^30,(-3922618975857373908637398671 : Int)/10^30)
theorem v4392_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 88 5) 1) 14) v4392_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4392 : Material (70 : Basis) (88 : Basis) where
  plus := ![v4392_pa,v4392_pb,v4392_pg]
  minus := ![(Primitive.Addresses.material4392 1).one,v4392_mb,v4392_mg]
  upper := v4392_upper
  lower := (Primitive.Addresses.material4392 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4392_pa_checked.trans (by decide +kernel)
    · exact v4392_pb_checked.trans (by decide +kernel)
    · exact v4392_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 88 Primitive.Addresses.material4392
    · exact v4392_mb_checked.trans (by decide +kernel)
    · exact v4392_mg_checked.trans (by decide +kernel)
  upper_error := v4392_upper_checked
  lower_error := reuse_lower_error 70 88 Primitive.Addresses.material4392

def v4393_pa : Scalar.QComplex := ((999997551740530351650081904497 : Int)/10^30,(-2212806576572446178649574179 : Int)/10^30)
theorem v4393_pa_checked : Scalar.distance (sourceCoefficient 70 89 1 0) v4393_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4393_pb : Scalar.QComplex := ((-954776277741184555528021 : Int)/10^30,(-431476456329061511008022576 : Int)/10^30)
theorem v4393_pb_checked : Scalar.distance (sourceCoefficient 70 89 1 1) v4393_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4393_pg : Scalar.QComplex := ((-93086201101639257406365 : Int)/10^30,(205982262283876849366 : Int)/10^30)
theorem v4393_pg_checked : Scalar.distance (sourceCoefficient 70 89 1 2) v4393_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4393_mb : Scalar.QComplex := ((-1327120671068114004118956 : Int)/10^30,(-431475471741731208099142752 : Int)/10^30)
theorem v4393_mb_checked : Scalar.distance (sourceCoefficient 70 89 3 1) v4393_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4393_mg : Scalar.QComplex := ((-93085988687977083437060 : Int)/10^30,(286311384691114751135 : Int)/10^30)
theorem v4393_mg_checked : Scalar.distance (sourceCoefficient 70 89 3 2) v4393_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4393_upper : Scalar.QComplex := ((999992243258238078688551677358 : Int)/10^30,(-3938708336091904858743740017 : Int)/10^30)
theorem v4393_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 89 5) 1) 14) v4393_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4393 : Material (70 : Basis) (89 : Basis) where
  plus := ![v4393_pa,v4393_pb,v4393_pg]
  minus := ![(Primitive.Addresses.material4393 1).one,v4393_mb,v4393_mg]
  upper := v4393_upper
  lower := (Primitive.Addresses.material4393 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4393_pa_checked.trans (by decide +kernel)
    · exact v4393_pb_checked.trans (by decide +kernel)
    · exact v4393_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 89 Primitive.Addresses.material4393
    · exact v4393_mb_checked.trans (by decide +kernel)
    · exact v4393_mg_checked.trans (by decide +kernel)
  upper_error := v4393_upper_checked
  lower_error := reuse_lower_error 70 89 Primitive.Addresses.material4393

def v4394_pa : Scalar.QComplex := ((999997493415192444088692835860 : Int)/10^30,(-2239009453339673852888368909 : Int)/10^30)
theorem v4394_pa_checked : Scalar.distance (sourceCoefficient 70 90 1 0) v4394_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4394_pb : Scalar.QComplex := ((-966082226856549515758106 : Int)/10^30,(-431476429833079211209461289 : Int)/10^30)
theorem v4394_pb_checked : Scalar.distance (sourceCoefficient 70 90 1 1) v4394_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4394_pg : Scalar.QComplex := ((-93086195528885196146642 : Int)/10^30,(208421394190499482938 : Int)/10^30)
theorem v4394_pg_checked : Scalar.distance (sourceCoefficient 70 90 1 2) v4394_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4394_mb : Scalar.QComplex := ((-1338426593108918011316187 : Int)/10^30,(-431475435489233888451481917 : Int)/10^30)
theorem v4394_mb_checked : Scalar.distance (sourceCoefficient 70 90 3 1) v4394_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4394_mg : Scalar.QComplex := ((-93085981010364116176115 : Int)/10^30,(288750510880501334695 : Int)/10^30)
theorem v4394_mg_checked : Scalar.distance (sourceCoefficient 70 90 3 2) v4394_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4394_upper : Scalar.QComplex := ((999992139709198846043021353954 : Int)/10^30,(-3964911073168783599191299833 : Int)/10^30)
theorem v4394_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 90 5) 1) 14) v4394_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4394 : Material (70 : Basis) (90 : Basis) where
  plus := ![v4394_pa,v4394_pb,v4394_pg]
  minus := ![(Primitive.Addresses.material4394 1).one,v4394_mb,v4394_mg]
  upper := v4394_upper
  lower := (Primitive.Addresses.material4394 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4394_pa_checked.trans (by decide +kernel)
    · exact v4394_pb_checked.trans (by decide +kernel)
    · exact v4394_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 90 Primitive.Addresses.material4394
    · exact v4394_mb_checked.trans (by decide +kernel)
    · exact v4394_mg_checked.trans (by decide +kernel)
  upper_error := v4394_upper_checked
  lower_error := reuse_lower_error 70 90 Primitive.Addresses.material4394

def v4395_pa : Scalar.QComplex := ((999997460256070626748368213060 : Int)/10^30,(-2253770487083207076418421512 : Int)/10^30)
theorem v4395_pa_checked : Scalar.distance (sourceCoefficient 70 91 1 0) v4395_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4395_pb : Scalar.QComplex := ((-972451279174926768344889 : Int)/10^30,(-431476414732993165491761560 : Int)/10^30)
theorem v4395_pb_checked : Scalar.distance (sourceCoefficient 70 91 1 1) v4395_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4395_pg : Scalar.QComplex := ((-93086192356716063010509 : Int)/10^30,(209795445915227242326 : Int)/10^30)
theorem v4395_pg_checked : Scalar.distance (sourceCoefficient 70 91 1 2) v4395_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4395_mb : Scalar.QComplex := ((-1344795630025111830875793 : Int)/10^30,(-431475414892948165894348737 : Int)/10^30)
theorem v4395_mb_checked : Scalar.distance (sourceCoefficient 70 91 3 1) v4395_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4395_mg : Scalar.QComplex := ((-93085976652451410735872 : Int)/10^30,(290124559356167746998 : Int)/10^30)
theorem v4395_mg_checked : Scalar.distance (sourceCoefficient 70 91 3 2) v4395_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4395_upper : Scalar.QComplex := ((999992081073921284501811784316 : Int)/10^30,(-3979672027697854929858992614 : Int)/10^30)
theorem v4395_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 91 5) 1) 14) v4395_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4395 : Material (70 : Basis) (91 : Basis) where
  plus := ![v4395_pa,v4395_pb,v4395_pg]
  minus := ![(Primitive.Addresses.material4395 1).one,v4395_mb,v4395_mg]
  upper := v4395_upper
  lower := (Primitive.Addresses.material4395 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4395_pa_checked.trans (by decide +kernel)
    · exact v4395_pb_checked.trans (by decide +kernel)
    · exact v4395_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 91 Primitive.Addresses.material4395
    · exact v4395_mb_checked.trans (by decide +kernel)
    · exact v4395_mg_checked.trans (by decide +kernel)
  upper_error := v4395_upper_checked
  lower_error := reuse_lower_error 70 91 Primitive.Addresses.material4395

def v4396_pa : Scalar.QComplex := ((999997387723750106916570368296 : Int)/10^30,(-2285726509405480274068022548 : Int)/10^30)
theorem v4396_pa_checked : Scalar.distance (sourceCoefficient 70 92 1 0) v4396_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4396_pb : Scalar.QComplex := ((-986239579966619523382781 : Int)/10^30,(-431476381613524398505206281 : Int)/10^30)
theorem v4396_pb_checked : Scalar.distance (sourceCoefficient 70 92 1 1) v4396_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4396_pg : Scalar.QComplex := ((-93086185408251942751984 : Int)/10^30,(212770117461399596246 : Int)/10^30)
theorem v4396_pg_checked : Scalar.distance (sourceCoefficient 70 92 1 2) v4396_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4396_mb : Scalar.QComplex := ((-1358583897102180144281314 : Int)/10^30,(-431475369874809149583781752 : Int)/10^30)
theorem v4396_mb_checked : Scalar.distance (sourceCoefficient 70 92 3 1) v4396_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4396_mg : Scalar.QComplex := ((-93085967136982307594440 : Int)/10^30,(293099223798522346497 : Int)/10^30)
theorem v4396_mg_checked : Scalar.distance (sourceCoefficient 70 92 3 2) v4396_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4396_upper : Scalar.QComplex := ((999991953388513292496759215930 : Int)/10^30,(-4011627877241181560043083785 : Int)/10^30)
theorem v4396_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 92 5) 1) 14) v4396_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4396 : Material (70 : Basis) (92 : Basis) where
  plus := ![v4396_pa,v4396_pb,v4396_pg]
  minus := ![(Primitive.Addresses.material4396 1).one,v4396_mb,v4396_mg]
  upper := v4396_upper
  lower := (Primitive.Addresses.material4396 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4396_pa_checked.trans (by decide +kernel)
    · exact v4396_pb_checked.trans (by decide +kernel)
    · exact v4396_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 92 Primitive.Addresses.material4396
    · exact v4396_mb_checked.trans (by decide +kernel)
    · exact v4396_mg_checked.trans (by decide +kernel)
  upper_error := v4396_upper_checked
  lower_error := reuse_lower_error 70 92 Primitive.Addresses.material4396

def v4397_pa : Scalar.QComplex := ((999997300316999946965295986985 : Int)/10^30,(-2323652020380368535674195422 : Int)/10^30)
theorem v4397_pa_checked : Scalar.distance (sourceCoefficient 70 93 1 0) v4397_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4397_pb : Scalar.QComplex := ((-1002603579488895840715505 : Int)/10^30,(-431476341544865430414340314 : Int)/10^30)
theorem v4397_pb_checked : Scalar.distance (sourceCoefficient 70 93 1 1) v4397_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4397_pg : Scalar.QComplex := ((-93086177017879171380906 : Int)/10^30,(216300467239773876285 : Int)/10^30)
theorem v4397_pg_checked : Scalar.distance (sourceCoefficient 70 93 1 2) v4397_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4397_mb : Scalar.QComplex := ((-1374947855953943503693446 : Int)/10^30,(-431475315684770520340906728 : Int)/10^30)
theorem v4397_mb_checked : Scalar.distance (sourceCoefficient 70 93 3 1) v4397_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4397_mg : Scalar.QComplex := ((-93085955700079802657222 : Int)/10^30,(296629565021872245760 : Int)/10^30)
theorem v4397_mg_checked : Scalar.distance (sourceCoefficient 70 93 3 2) v4397_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4397_upper : Scalar.QComplex := ((999991800525901947454531568814 : Int)/10^30,(-4049553180874354970378961256 : Int)/10^30)
theorem v4397_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 93 5) 1) 14) v4397_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4397 : Material (70 : Basis) (93 : Basis) where
  plus := ![v4397_pa,v4397_pb,v4397_pg]
  minus := ![(Primitive.Addresses.material4397 1).one,v4397_mb,v4397_mg]
  upper := v4397_upper
  lower := (Primitive.Addresses.material4397 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4397_pa_checked.trans (by decide +kernel)
    · exact v4397_pb_checked.trans (by decide +kernel)
    · exact v4397_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 93 Primitive.Addresses.material4397
    · exact v4397_mb_checked.trans (by decide +kernel)
    · exact v4397_mg_checked.trans (by decide +kernel)
  upper_error := v4397_upper_checked
  lower_error := reuse_lower_error 70 93 Primitive.Addresses.material4397

def v4398_pa : Scalar.QComplex := ((999997195217288676434428650172 : Int)/10^30,(-2368450454588626897825199698 : Int)/10^30)
theorem v4398_pa_checked : Scalar.distance (sourceCoefficient 70 94 1 0) v4398_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4398_pb : Scalar.QComplex := ((-1021933088952945859743738 : Int)/10^30,(-431476293148882262036286948 : Int)/10^30)
theorem v4398_pb_checked : Scalar.distance (sourceCoefficient 70 94 1 1) v4398_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4398_pg : Scalar.QComplex := ((-93086166905755765348725 : Int)/10^30,(220470592695956788189 : Int)/10^30)
theorem v4398_pg_checked : Scalar.distance (sourceCoefficient 70 94 1 2) v4398_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4398_mb : Scalar.QComplex := ((-1394277316457179946890729 : Int)/10^30,(-431475250608309273313254506 : Int)/10^30)
theorem v4398_mb_checked : Scalar.distance (sourceCoefficient 70 94 3 1) v4398_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4398_mg : Scalar.QComplex := ((-93085941989329708623387 : Int)/10^30,(300799680199019799904 : Int)/10^30)
theorem v4398_mg_checked : Scalar.distance (sourceCoefficient 70 94 3 2) v4398_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4398_upper : Scalar.QComplex := ((999991618108313849348294512596 : Int)/10^30,(-4094351366968040891464437435 : Int)/10^30)
theorem v4398_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 94 5) 1) 14) v4398_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4398 : Material (70 : Basis) (94 : Basis) where
  plus := ![v4398_pa,v4398_pb,v4398_pg]
  minus := ![(Primitive.Addresses.material4398 1).one,v4398_mb,v4398_mg]
  upper := v4398_upper
  lower := (Primitive.Addresses.material4398 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4398_pa_checked.trans (by decide +kernel)
    · exact v4398_pb_checked.trans (by decide +kernel)
    · exact v4398_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 94 Primitive.Addresses.material4398
    · exact v4398_mb_checked.trans (by decide +kernel)
    · exact v4398_mg_checked.trans (by decide +kernel)
  upper_error := v4398_upper_checked
  lower_error := reuse_lower_error 70 94 Primitive.Addresses.material4398

def v4399_pa : Scalar.QComplex := ((999997089375882831649132742271 : Int)/10^30,(-2412724551747246238577195190 : Int)/10^30)
theorem v4399_pa_checked : Scalar.distance (sourceCoefficient 70 95 1 0) v4399_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4399_pb : Scalar.QComplex := ((-1041036357906250756853142 : Int)/10^30,(-431476244184950719355477308 : Int)/10^30)
theorem v4399_pb_checked : Scalar.distance (sourceCoefficient 70 95 1 1) v4399_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4399_pg : Scalar.QComplex := ((-93086156697847266845689 : Int)/10^30,(224591909395315476917 : Int)/10^30)
theorem v4399_pg_checked : Scalar.distance (sourceCoefficient 70 95 1 2) v4399_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4399_mb : Scalar.QComplex := ((-1413380536043797082443673 : Int)/10^30,(-431475185159135234734670351 : Int)/10^30)
theorem v4399_mb_checked : Scalar.distance (sourceCoefficient 70 95 3 1) v4399_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4399_mg : Scalar.QComplex := ((-93085928224914316658366 : Int)/10^30,(304920986554858640908 : Int)/10^30)
theorem v4399_mg_checked : Scalar.distance (sourceCoefficient 70 95 3 2) v4399_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4399_upper : Scalar.QComplex := ((999991435853990461845956160706 : Int)/10^30,(-4138625215512928684474730605 : Int)/10^30)
theorem v4399_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 95 5) 1) 14) v4399_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4399 : Material (70 : Basis) (95 : Basis) where
  plus := ![v4399_pa,v4399_pb,v4399_pg]
  minus := ![(Primitive.Addresses.material4399 1).one,v4399_mb,v4399_mg]
  upper := v4399_upper
  lower := (Primitive.Addresses.material4399 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4399_pa_checked.trans (by decide +kernel)
    · exact v4399_pb_checked.trans (by decide +kernel)
    · exact v4399_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 95 Primitive.Addresses.material4399
    · exact v4399_mb_checked.trans (by decide +kernel)
    · exact v4399_mg_checked.trans (by decide +kernel)
  upper_error := v4399_upper_checked
  lower_error := reuse_lower_error 70 95 Primitive.Addresses.material4399

def v4400_pa : Scalar.QComplex := ((999997037845394534837216492920 : Int)/10^30,(-2433988585957300435043648427 : Int)/10^30)
theorem v4400_pa_checked : Scalar.distance (sourceCoefficient 70 96 1 0) v4400_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4400_pb : Scalar.QComplex := ((-1050211306131593004205142 : Int)/10^30,(-431476220267599760148346101 : Int)/10^30)
theorem v4400_pb_checked : Scalar.distance (sourceCoefficient 70 96 1 1) v4400_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4400_pg : Scalar.QComplex := ((-93086151719502728228565 : Int)/10^30,(226571301935184669468 : Int)/10^30)
theorem v4400_pg_checked : Scalar.distance (sourceCoefficient 70 96 1 2) v4400_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4400_mb : Scalar.QComplex := ((-1422555460213290109356230 : Int)/10^30,(-431475153324226086908480027 : Int)/10^30)
theorem v4400_mb_checked : Scalar.distance (sourceCoefficient 70 96 3 1) v4400_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4400_mg : Scalar.QComplex := ((-93085921538445018329968 : Int)/10^30,(306900374061622407645 : Int)/10^30)
theorem v4400_mg_checked : Scalar.distance (sourceCoefficient 70 96 3 2) v4400_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4400_upper : Scalar.QComplex := ((999991347623784925204179629268 : Int)/10^30,(-4159889129115753783071400378 : Int)/10^30)
theorem v4400_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 96 5) 1) 14) v4400_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4400 : Material (70 : Basis) (96 : Basis) where
  plus := ![v4400_pa,v4400_pb,v4400_pg]
  minus := ![(Primitive.Addresses.material4400 1).one,v4400_mb,v4400_mg]
  upper := v4400_upper
  lower := (Primitive.Addresses.material4400 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4400_pa_checked.trans (by decide +kernel)
    · exact v4400_pb_checked.trans (by decide +kernel)
    · exact v4400_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 96 Primitive.Addresses.material4400
    · exact v4400_mb_checked.trans (by decide +kernel)
    · exact v4400_mg_checked.trans (by decide +kernel)
  upper_error := v4400_upper_checked
  lower_error := reuse_lower_error 70 96 Primitive.Addresses.material4400

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
