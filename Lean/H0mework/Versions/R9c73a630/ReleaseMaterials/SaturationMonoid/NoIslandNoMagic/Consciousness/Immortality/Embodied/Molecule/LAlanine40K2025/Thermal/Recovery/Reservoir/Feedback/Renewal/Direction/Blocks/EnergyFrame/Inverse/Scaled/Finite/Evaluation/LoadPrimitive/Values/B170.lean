import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B113
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B114

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2721_pa : Scalar.QComplex := ((999999005946065689953954077823 : Int)/10^30,(-1410002439883303100719951888 : Int)/10^30)
theorem v2721_pa_checked : Scalar.distance (sourceCoefficient 33 82 1 0) v2721_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2721_pb : Scalar.QComplex := ((-608384292428586781667422 : Int)/10^30,(-431477046034146830256459059 : Int)/10^30)
theorem v2721_pb_checked : Scalar.distance (sourceCoefficient 33 82 1 1) v2721_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2721_pg : Scalar.QComplex := ((-93086332396165098966391 : Int)/10^30,(131252086270033692958 : Int)/10^30)
theorem v2721_pg_checked : Scalar.distance (sourceCoefficient 33 82 1 2) v2721_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2721_mb : Scalar.QComplex := ((-980729323622012557326751 : Int)/10^30,(-431476360367279362080080574 : Int)/10^30)
theorem v2721_mb_checked : Scalar.distance (sourceCoefficient 33 82 3 1) v2721_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2721_mg : Scalar.QComplex := ((-93086184471230215805120 : Int)/10^30,(211581349803993977780 : Int)/10^30)
theorem v2721_mg_checked : Scalar.distance (sourceCoefficient 33 82 3 2) v2721_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2721_upper : Scalar.QComplex := ((999995083028717651766383891259 : Int)/10^30,(-3135907904912048879186846474 : Int)/10^30)
theorem v2721_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 82 5) 1) 14) v2721_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2721 : Material (33 : Basis) (82 : Basis) where
  plus := ![v2721_pa,v2721_pb,v2721_pg]
  minus := ![(Primitive.Addresses.material2721 1).one,v2721_mb,v2721_mg]
  upper := v2721_upper
  lower := (Primitive.Addresses.material2721 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2721_pa_checked.trans (by decide +kernel)
    · exact v2721_pb_checked.trans (by decide +kernel)
    · exact v2721_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 82 Primitive.Addresses.material2721
    · exact v2721_mb_checked.trans (by decide +kernel)
    · exact v2721_mg_checked.trans (by decide +kernel)
  upper_error := v2721_upper_checked
  lower_error := reuse_lower_error 33 82 Primitive.Addresses.material2721

def v2722_pa : Scalar.QComplex := ((999998986722223586303124290567 : Int)/10^30,(-1423571047083896539280329431 : Int)/10^30)
theorem v2722_pa_checked : Scalar.distance (sourceCoefficient 33 83 1 0) v2722_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2722_pb : Scalar.QComplex := ((-614238838559953015213786 : Int)/10^30,(-431477036164524538928562714 : Int)/10^30)
theorem v2722_pb_checked : Scalar.distance (sourceCoefficient 33 83 1 1) v2722_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2722_pg : Scalar.QComplex := ((-93086330436795592273046 : Int)/10^30,(132515139163752242594 : Int)/10^30)
theorem v2722_pg_checked : Scalar.distance (sourceCoefficient 33 83 1 2) v2722_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2722_mb : Scalar.QComplex := ((-986583859056424174060227 : Int)/10^30,(-431476345445451113264101048 : Int)/10^30)
theorem v2722_mb_checked : Scalar.distance (sourceCoefficient 33 83 3 1) v2722_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2722_mg : Scalar.QComplex := ((-93086181421903677186115 : Int)/10^30,(212844400536572573165 : Int)/10^30)
theorem v2722_mg_checked : Scalar.distance (sourceCoefficient 33 83 3 2) v2722_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2722_upper : Scalar.QComplex := ((999995040386719085975607170749 : Int)/10^30,(-3149476458725188275460220985 : Int)/10^30)
theorem v2722_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 83 5) 1) 14) v2722_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2722 : Material (33 : Basis) (83 : Basis) where
  plus := ![v2722_pa,v2722_pb,v2722_pg]
  minus := ![(Primitive.Addresses.material2722 1).one,v2722_mb,v2722_mg]
  upper := v2722_upper
  lower := (Primitive.Addresses.material2722 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2722_pa_checked.trans (by decide +kernel)
    · exact v2722_pb_checked.trans (by decide +kernel)
    · exact v2722_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 83 Primitive.Addresses.material2722
    · exact v2722_mb_checked.trans (by decide +kernel)
    · exact v2722_mg_checked.trans (by decide +kernel)
  upper_error := v2722_upper_checked
  lower_error := reuse_lower_error 33 83 Primitive.Addresses.material2722

def v2723_pa : Scalar.QComplex := ((999998936081903119739198086277 : Int)/10^30,(-1458710067778653790186372310 : Int)/10^30)
theorem v2723_pa_checked : Scalar.distance (sourceCoefficient 33 84 1 0) v2723_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2723_pb : Scalar.QComplex := ((-629400528296814816300064 : Int)/10^30,(-431477010112545803126818899 : Int)/10^30)
theorem v2723_pb_checked : Scalar.distance (sourceCoefficient 33 84 1 1) v2723_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2723_pg : Scalar.QComplex := ((-93086325269621334191016 : Int)/10^30,(135786104308608828248 : Int)/10^30)
theorem v2723_pg_checked : Scalar.distance (sourceCoefficient 33 84 1 2) v2723_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2723_mb : Scalar.QComplex := ((-1001745520666211651229787 : Int)/10^30,(-431476306309626692049839540 : Int)/10^30)
theorem v2723_mb_checked : Scalar.distance (sourceCoefficient 33 84 3 1) v2723_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2723_mg : Scalar.QComplex := ((-93086173432035741869373 : Int)/10^30,(216115360004460681062 : Int)/10^30)
theorem v2723_mg_checked : Scalar.distance (sourceCoefficient 33 84 3 2) v2723_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2723_upper : Scalar.QComplex := ((999994929099712110125173398176 : Int)/10^30,(-3184615339683902849549222632 : Int)/10^30)
theorem v2723_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 84 5) 1) 14) v2723_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2723 : Material (33 : Basis) (84 : Basis) where
  plus := ![v2723_pa,v2723_pb,v2723_pg]
  minus := ![(Primitive.Addresses.material2723 1).one,v2723_mb,v2723_mg]
  upper := v2723_upper
  lower := (Primitive.Addresses.material2723 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2723_pa_checked.trans (by decide +kernel)
    · exact v2723_pb_checked.trans (by decide +kernel)
    · exact v2723_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 84 Primitive.Addresses.material2723
    · exact v2723_mb_checked.trans (by decide +kernel)
    · exact v2723_mg_checked.trans (by decide +kernel)
  upper_error := v2723_upper_checked
  lower_error := reuse_lower_error 33 84 Primitive.Addresses.material2723

def v2724_pa : Scalar.QComplex := ((999998817635940839291956365349 : Int)/10^30,(-1537766796473590039740558752 : Int)/10^30)
theorem v2724_pa_checked : Scalar.distance (sourceCoefficient 33 85 1 0) v2724_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2724_pb : Scalar.QComplex := ((-663511709979446423869914 : Int)/10^30,(-431476948903183709092761048 : Int)/10^30)
theorem v2724_pb_checked : Scalar.distance (sourceCoefficient 33 85 1 1) v2724_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2724_pg : Scalar.QComplex := ((-93086313154149171504415 : Int)/10^30,(143145210824345896005 : Int)/10^30)
theorem v2724_pg_checked : Scalar.distance (sourceCoefficient 33 85 1 2) v2724_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2724_mb : Scalar.QComplex := ((-1035856636826768640520214 : Int)/10^30,(-431476215663873907540073799 : Int)/10^30)
theorem v2724_mb_checked : Scalar.distance (sourceCoefficient 33 85 3 1) v2724_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2724_mg : Scalar.QComplex := ((-93086154965990609099441 : Int)/10^30,(223474453324959249440 : Int)/10^30)
theorem v2724_mg_checked : Scalar.distance (sourceCoefficient 33 85 3 2) v2724_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2724_upper : Scalar.QComplex := ((999994674209184483967987919691 : Int)/10^30,(-3263671746206142801408557577 : Int)/10^30)
theorem v2724_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 85 5) 1) 14) v2724_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2724 : Material (33 : Basis) (85 : Basis) where
  plus := ![v2724_pa,v2724_pb,v2724_pg]
  minus := ![(Primitive.Addresses.material2724 1).one,v2724_mb,v2724_mg]
  upper := v2724_upper
  lower := (Primitive.Addresses.material2724 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2724_pa_checked.trans (by decide +kernel)
    · exact v2724_pb_checked.trans (by decide +kernel)
    · exact v2724_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 85 Primitive.Addresses.material2724
    · exact v2724_mb_checked.trans (by decide +kernel)
    · exact v2724_mg_checked.trans (by decide +kernel)
  upper_error := v2724_upper_checked
  lower_error := reuse_lower_error 33 85 Primitive.Addresses.material2724

def v2725_pa : Scalar.QComplex := ((999998795101803607779725071187 : Int)/10^30,(-1552351423165765284838060936 : Int)/10^30)
theorem v2725_pa_checked : Scalar.distance (sourceCoefficient 33 86 1 0) v2725_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2725_pb : Scalar.QComplex := ((-669804644600348489596335 : Int)/10^30,(-431476937218239905014923675 : Int)/10^30)
theorem v2725_pb_checked : Scalar.distance (sourceCoefficient 33 86 1 1) v2725_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2725_pg : Scalar.QComplex := ((-93086310844890269388442 : Int)/10^30,(144502841228528990602 : Int)/10^30)
theorem v2725_pg_checked : Scalar.distance (sourceCoefficient 33 86 1 2) v2725_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2725_mb : Scalar.QComplex := ((-1042149559020943312978516 : Int)/10^30,(-431476198548415299716519958 : Int)/10^30)
theorem v2725_mb_checked : Scalar.distance (sourceCoefficient 33 86 3 1) v2725_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2725_mg : Scalar.QComplex := ((-93086151485158673419665 : Int)/10^30,(224832081230848070418 : Int)/10^30)
theorem v2725_mg_checked : Scalar.distance (sourceCoefficient 33 86 3 2) v2725_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2725_upper : Scalar.QComplex := ((999994626503338250709613688838 : Int)/10^30,(-3278256312284353238480665798 : Int)/10^30)
theorem v2725_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 86 5) 1) 14) v2725_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2725 : Material (33 : Basis) (86 : Basis) where
  plus := ![v2725_pa,v2725_pb,v2725_pg]
  minus := ![(Primitive.Addresses.material2725 1).one,v2725_mb,v2725_mg]
  upper := v2725_upper
  lower := (Primitive.Addresses.material2725 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2725_pa_checked.trans (by decide +kernel)
    · exact v2725_pb_checked.trans (by decide +kernel)
    · exact v2725_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 86 Primitive.Addresses.material2725
    · exact v2725_mb_checked.trans (by decide +kernel)
    · exact v2725_mg_checked.trans (by decide +kernel)
  upper_error := v2725_upper_checked
  lower_error := reuse_lower_error 33 86 Primitive.Addresses.material2725

def v2726_pa : Scalar.QComplex := ((999998793602143880879909180313 : Int)/10^30,(-1553317178441818730931136835 : Int)/10^30)
theorem v2726_pa_checked : Scalar.distance (sourceCoefficient 33 87 1 0) v2726_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2726_pb : Scalar.QComplex := ((-670221346027566025369073 : Int)/10^30,(-431476936440174010589885225 : Int)/10^30)
theorem v2726_pb_checked : Scalar.distance (sourceCoefficient 33 87 1 1) v2726_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2726_pg : Scalar.QComplex := ((-93086310691161794350586 : Int)/10^30,(144592739910725382287 : Int)/10^30)
theorem v2726_pg_checked : Scalar.distance (sourceCoefficient 33 87 1 2) v2726_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2726_mb : Scalar.QComplex := ((-1042566259621568039100366 : Int)/10^30,(-431476197410755130847838208 : Int)/10^30)
theorem v2726_mb_checked : Scalar.distance (sourceCoefficient 33 87 3 1) v2726_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2726_mg : Scalar.QComplex := ((-93086151253851741772805 : Int)/10^30,(224921979746910323865 : Int)/10^30)
theorem v2726_mg_checked : Scalar.distance (sourceCoefficient 33 87 3 2) v2726_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2726_upper : Scalar.QComplex := ((999994623336874763542801880545 : Int)/10^30,(-3279222063533751005914569537 : Int)/10^30)
theorem v2726_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 87 5) 1) 14) v2726_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2726 : Material (33 : Basis) (87 : Basis) where
  plus := ![v2726_pa,v2726_pb,v2726_pg]
  minus := ![(Primitive.Addresses.material2726 1).one,v2726_mb,v2726_mg]
  upper := v2726_upper
  lower := (Primitive.Addresses.material2726 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2726_pa_checked.trans (by decide +kernel)
    · exact v2726_pb_checked.trans (by decide +kernel)
    · exact v2726_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 87 Primitive.Addresses.material2726
    · exact v2726_mb_checked.trans (by decide +kernel)
    · exact v2726_mg_checked.trans (by decide +kernel)
  upper_error := v2726_upper_checked
  lower_error := reuse_lower_error 33 87 Primitive.Addresses.material2726

def v2727_pa : Scalar.QComplex := ((999998775266621263259059939355 : Int)/10^30,(-1565076757702839598401236943 : Int)/10^30)
theorem v2727_pa_checked : Scalar.distance (sourceCoefficient 33 88 1 0) v2727_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2727_pb : Scalar.QComplex := ((-675295336868911758488573 : Int)/10^30,(-431476926922960571334251193 : Int)/10^30)
theorem v2727_pb_checked : Scalar.distance (sourceCoefficient 33 88 1 1) v2727_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2727_pg : Scalar.QComplex := ((-93086308811151657189867 : Int)/10^30,(145687396808900238096 : Int)/10^30)
theorem v2727_pg_checked : Scalar.distance (sourceCoefficient 33 88 1 2) v2727_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2727_mb : Scalar.QComplex := ((-1047640240360708530453512 : Int)/10^30,(-431476183514919663268640259 : Int)/10^30)
theorem v2727_mb_checked : Scalar.distance (sourceCoefficient 33 88 3 1) v2727_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2727_mg : Scalar.QComplex := ((-93086148429202703017415 : Int)/10^30,(226016634615130312336 : Int)/10^30)
theorem v2727_mg_checked : Scalar.distance (sourceCoefficient 33 88 3 2) v2727_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2727_upper : Scalar.QComplex := ((999994584705412470704046406270 : Int)/10^30,(-3290981593634811288915173398 : Int)/10^30)
theorem v2727_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 88 5) 1) 14) v2727_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2727 : Material (33 : Basis) (88 : Basis) where
  plus := ![v2727_pa,v2727_pb,v2727_pg]
  minus := ![(Primitive.Addresses.material2727 1).one,v2727_mb,v2727_mg]
  upper := v2727_upper
  lower := (Primitive.Addresses.material2727 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2727_pa_checked.trans (by decide +kernel)
    · exact v2727_pb_checked.trans (by decide +kernel)
    · exact v2727_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 88 Primitive.Addresses.material2727
    · exact v2727_mb_checked.trans (by decide +kernel)
    · exact v2727_mg_checked.trans (by decide +kernel)
  upper_error := v2727_upper_checked
  lower_error := reuse_lower_error 33 88 Primitive.Addresses.material2727

def v2728_pa : Scalar.QComplex := ((999998749955907389453327973413 : Int)/10^30,(-1581166222321631772571708297 : Int)/10^30)
theorem v2728_pa_checked : Scalar.distance (sourceCoefficient 33 89 1 0) v2728_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2728_pb : Scalar.QComplex := ((-682237574595887643423451 : Int)/10^30,(-431476913772612249926041741 : Int)/10^30)
theorem v2728_pb_checked : Scalar.distance (sourceCoefficient 33 89 1 1) v2728_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2728_pg : Scalar.QComplex := ((-93086306214589666133450 : Int)/10^30,(147185107135071071796 : Int)/10^30)
theorem v2728_pg_checked : Scalar.distance (sourceCoefficient 33 89 1 2) v2728_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2728_mb : Scalar.QComplex := ((-1054582464154613702024423 : Int)/10^30,(-431476164373737746736409299 : Int)/10^30)
theorem v2728_mb_checked : Scalar.distance (sourceCoefficient 33 89 3 1) v2728_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2728_mg : Scalar.QComplex := ((-93086144540185121663334 : Int)/10^30,(227514342142919089388 : Int)/10^30)
theorem v2728_mg_checked : Scalar.distance (sourceCoefficient 33 89 3 2) v2728_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2728_upper : Scalar.QComplex := ((999994531625779987026384936968 : Int)/10^30,(-3307070990606239938511415695 : Int)/10^30)
theorem v2728_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 89 5) 1) 14) v2728_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2728 : Material (33 : Basis) (89 : Basis) where
  plus := ![v2728_pa,v2728_pb,v2728_pg]
  minus := ![(Primitive.Addresses.material2728 1).one,v2728_mb,v2728_mg]
  upper := v2728_upper
  lower := (Primitive.Addresses.material2728 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2728_pa_checked.trans (by decide +kernel)
    · exact v2728_pb_checked.trans (by decide +kernel)
    · exact v2728_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 89 Primitive.Addresses.material2728
    · exact v2728_mb_checked.trans (by decide +kernel)
    · exact v2728_mg_checked.trans (by decide +kernel)
  upper_error := v2728_upper_checked
  lower_error := reuse_lower_error 33 89 Primitive.Addresses.material2728

def v2729_pa : Scalar.QComplex := ((999998708181404434755249832253 : Int)/10^30,(-1607369130702467376513772787 : Int)/10^30)
theorem v2729_pa_checked : Scalar.distance (sourceCoefficient 33 90 1 0) v2729_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2729_pb : Scalar.QComplex := ((-693543532804959584352678 : Int)/10^30,(-431476892037505182468967032 : Int)/10^30)
theorem v2729_pb_checked : Scalar.distance (sourceCoefficient 33 90 1 1) v2729_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2729_pg : Scalar.QComplex := ((-93086301925717348377968 : Int)/10^30,(149624241494025218518 : Int)/10^30)
theorem v2729_pg_checked : Scalar.distance (sourceCoefficient 33 90 1 2) v2729_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2729_mb : Scalar.QComplex := ((-1065888399397542207568036 : Int)/10^30,(-431476132882106039279244311 : Int)/10^30)
theorem v2729_mb_checked : Scalar.distance (sourceCoefficient 33 90 3 1) v2729_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2729_mg : Scalar.QComplex := ((-93086138146451303607134 : Int)/10^30,(229953471892568393740 : Int)/10^30)
theorem v2729_mg_checked : Scalar.distance (sourceCoefficient 33 90 3 2) v2729_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2729_upper : Scalar.QComplex := ((999994444627496494500378337371 : Int)/10^30,(-3333273787861919172530898369 : Int)/10^30)
theorem v2729_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 90 5) 1) 14) v2729_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2729 : Material (33 : Basis) (90 : Basis) where
  plus := ![v2729_pa,v2729_pb,v2729_pg]
  minus := ![(Primitive.Addresses.material2729 1).one,v2729_mb,v2729_mg]
  upper := v2729_upper
  lower := (Primitive.Addresses.material2729 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2729_pa_checked.trans (by decide +kernel)
    · exact v2729_pb_checked.trans (by decide +kernel)
    · exact v2729_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 90 Primitive.Addresses.material2729
    · exact v2729_mb_checked.trans (by decide +kernel)
    · exact v2729_mg_checked.trans (by decide +kernel)
  upper_error := v2729_upper_checked
  lower_error := reuse_lower_error 33 90 Primitive.Addresses.material2729

def v2730_pa : Scalar.QComplex := ((999998684345970125985269808232 : Int)/10^30,(-1622130182446064695826527159 : Int)/10^30)
theorem v2730_pa_checked : Scalar.distance (sourceCoefficient 33 91 1 0) v2730_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2730_pb : Scalar.QComplex := ((-699912590301085243200538 : Int)/10^30,(-431476879619393365651522612 : Int)/10^30)
theorem v2730_pb_checked : Scalar.distance (sourceCoefficient 33 91 1 1) v2730_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2730_pg : Scalar.QComplex := ((-93086299476805512443832 : Int)/10^30,(150998294615054356941 : Int)/10^30)
theorem v2730_pg_checked : Scalar.distance (sourceCoefficient 33 91 1 2) v2730_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2730_mb : Scalar.QComplex := ((-1072257443805905473381998 : Int)/10^30,(-431476114967789078837111270 : Int)/10^30)
theorem v2730_mb_checked : Scalar.distance (sourceCoefficient 33 91 3 1) v2730_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2730_mg : Scalar.QComplex := ((-93086134511794421121939 : Int)/10^30,(231327522388674138357 : Int)/10^30)
theorem v2730_mg_checked : Scalar.distance (sourceCoefficient 33 91 3 2) v2730_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2730_upper : Scalar.QComplex := ((999994395315861488514530359859 : Int)/10^30,(-3348034776482866591469221969 : Int)/10^30)
theorem v2730_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 91 5) 1) 14) v2730_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2730 : Material (33 : Basis) (91 : Basis) where
  plus := ![v2730_pa,v2730_pb,v2730_pg]
  minus := ![(Primitive.Addresses.material2730 1).one,v2730_mb,v2730_mg]
  upper := v2730_upper
  lower := (Primitive.Addresses.material2730 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2730_pa_checked.trans (by decide +kernel)
    · exact v2730_pb_checked.trans (by decide +kernel)
    · exact v2730_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 91 Primitive.Addresses.material2730
    · exact v2730_mb_checked.trans (by decide +kernel)
    · exact v2730_mg_checked.trans (by decide +kernel)
  upper_error := v2730_upper_checked
  lower_error := reuse_lower_error 33 91 Primitive.Addresses.material2730

def v2731_pa : Scalar.QComplex := ((999998631998412646771388504637 : Int)/10^30,(-1654086244207996012448034463 : Int)/10^30)
theorem v2731_pa_checked : Scalar.distance (sourceCoefficient 33 92 1 0) v2731_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2731_pb : Scalar.QComplex := ((-713700902437661284307853 : Int)/10^30,(-431476852306105260985514555 : Int)/10^30)
theorem v2731_pb_checked : Scalar.distance (sourceCoefficient 33 92 1 1) v2731_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2731_pg : Scalar.QComplex := ((-93086294094114281856059 : Int)/10^30,(153972969220640756294 : Int)/10^30)
theorem v2731_pg_checked : Scalar.distance (sourceCoefficient 33 92 1 2) v2731_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2731_mb : Scalar.QComplex := ((-1086045727238325259551372 : Int)/10^30,(-431476075755818772817354058 : Int)/10^30)
theorem v2731_mb_checked : Scalar.distance (sourceCoefficient 33 92 3 1) v2731_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2731_mg : Scalar.QComplex := ((-93086126562094984505922 : Int)/10^30,(234302191241633128121 : Int)/10^30)
theorem v2731_mg_checked : Scalar.distance (sourceCoefficient 33 92 3 2) v2731_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2731_upper : Scalar.QComplex := ((999994287815118405021938647233 : Int)/10^30,(-3379990700302862460594976472 : Int)/10^30)
theorem v2731_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 92 5) 1) 14) v2731_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2731 : Material (33 : Basis) (92 : Basis) where
  plus := ![v2731_pa,v2731_pb,v2731_pg]
  minus := ![(Primitive.Addresses.material2731 1).one,v2731_mb,v2731_mg]
  upper := v2731_upper
  lower := (Primitive.Addresses.material2731 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2731_pa_checked.trans (by decide +kernel)
    · exact v2731_pb_checked.trans (by decide +kernel)
    · exact v2731_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 92 Primitive.Addresses.material2731
    · exact v2731_mb_checked.trans (by decide +kernel)
    · exact v2731_mg_checked.trans (by decide +kernel)
  upper_error := v2731_upper_checked
  lower_error := reuse_lower_error 33 92 Primitive.Addresses.material2731

def v2732_pa : Scalar.QComplex := ((999998568547005018186164742011 : Int)/10^30,(-1692011802827022488885472709 : Int)/10^30)
theorem v2732_pa_checked : Scalar.distance (sourceCoefficient 33 93 1 0) v2732_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2732_pb : Scalar.QComplex := ((-730064915664853170669947 : Int)/10^30,(-431476819128240382225605865 : Int)/10^30)
theorem v2732_pb_checked : Scalar.distance (sourceCoefficient 33 93 1 1) v2732_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2732_pg : Scalar.QComplex := ((-93086287562005870984157 : Int)/10^30,(157503322694867184874 : Int)/10^30)
theorem v2732_pg_checked : Scalar.distance (sourceCoefficient 33 93 1 2) v2732_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2732_mb : Scalar.QComplex := ((-1102409705741444034274022 : Int)/10^30,(-431476028456559840422982418 : Int)/10^30)
theorem v2732_mb_checked : Scalar.distance (sourceCoefficient 33 93 3 1) v2732_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2732_mg : Scalar.QComplex := ((-93086116983452958797182 : Int)/10^30,(237832537764432249782 : Int)/10^30)
theorem v2732_mg_checked : Scalar.distance (sourceCoefficient 33 93 3 2) v2732_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2732_upper : Scalar.QComplex := ((999994158907731683216737011556 : Int)/10^30,(-3417916092924851122854477942 : Int)/10^30)
theorem v2732_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 93 5) 1) 14) v2732_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2732 : Material (33 : Basis) (93 : Basis) where
  plus := ![v2732_pa,v2732_pb,v2732_pg]
  minus := ![(Primitive.Addresses.material2732 1).one,v2732_mb,v2732_mg]
  upper := v2732_upper
  lower := (Primitive.Addresses.material2732 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2732_pa_checked.trans (by decide +kernel)
    · exact v2732_pb_checked.trans (by decide +kernel)
    · exact v2732_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 93 Primitive.Addresses.material2732
    · exact v2732_mb_checked.trans (by decide +kernel)
    · exact v2732_mg_checked.trans (by decide +kernel)
  upper_error := v2732_upper_checked
  lower_error := reuse_lower_error 33 93 Primitive.Addresses.material2732

def v2733_pa : Scalar.QComplex := ((999998491743863068950809388453 : Int)/10^30,(-1736810294483978405881400489 : Int)/10^30)
theorem v2733_pa_checked : Scalar.distance (sourceCoefficient 33 94 1 0) v2733_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2733_pb : Scalar.QComplex := ((-749394441654116449852803 : Int)/10^30,(-431476778871812352006573592 : Int)/10^30)
theorem v2733_pb_checked : Scalar.distance (sourceCoefficient 33 94 1 1) v2733_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2733_pg : Scalar.QComplex := ((-93086279644904557609330 : Int)/10^30,(161673452607461723571 : Int)/10^30)
theorem v2733_pg_checked : Scalar.distance (sourceCoefficient 33 94 1 2) v2733_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2733_mb : Scalar.QComplex := ((-1121739189793957076810138 : Int)/10^30,(-431475971519636440311201769 : Int)/10^30)
theorem v2733_mb_checked : Scalar.distance (sourceCoefficient 33 94 3 1) v2733_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2733_mg : Scalar.QComplex := ((-93086105467720294431135 : Int)/10^30,(242002659292194977232 : Int)/10^30)
theorem v2733_mg_checked : Scalar.distance (sourceCoefficient 33 94 3 2) v2733_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2733_upper : Scalar.QComplex := ((999994004786571610749681864286 : Int)/10^30,(-3462714385304460639538146368 : Int)/10^30)
theorem v2733_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 94 5) 1) 14) v2733_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2733 : Material (33 : Basis) (94 : Basis) where
  plus := ![v2733_pa,v2733_pb,v2733_pg]
  minus := ![(Primitive.Addresses.material2733 1).one,v2733_mb,v2733_mg]
  upper := v2733_upper
  lower := (Primitive.Addresses.material2733 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2733_pa_checked.trans (by decide +kernel)
    · exact v2733_pb_checked.trans (by decide +kernel)
    · exact v2733_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 94 Primitive.Addresses.material2733
    · exact v2733_mb_checked.trans (by decide +kernel)
    · exact v2733_mg_checked.trans (by decide +kernel)
  upper_error := v2733_upper_checked
  lower_error := reuse_lower_error 33 94 Primitive.Addresses.material2733

def v2734_pa : Scalar.QComplex := ((999998413867833674245391221703 : Int)/10^30,(-1781084449664377976073135963 : Int)/10^30)
theorem v2734_pa_checked : Scalar.distance (sourceCoefficient 33 95 1 0) v2734_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2734_pb : Scalar.QComplex := ((-768497727297482671094300 : Int)/10^30,(-431476737952167710176783154 : Int)/10^30)
theorem v2734_pb_checked : Scalar.distance (sourceCoefficient 33 95 1 1) v2734_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2734_pg : Scalar.QComplex := ((-93086271606326841729638 : Int)/10^30,(165794773807687201621 : Int)/10^30)
theorem v2734_pg_checked : Scalar.distance (sourceCoefficient 33 95 1 2) v2734_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2734_mb : Scalar.QComplex := ((-1140842433012486616224237 : Int)/10^30,(-431475914114731904556751287 : Int)/10^30)
theorem v2734_mb_checked : Scalar.distance (sourceCoefficient 33 95 3 1) v2734_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2734_mg : Scalar.QComplex := ((-93086093872630993303135 : Int)/10^30,(246123972020933694051 : Int)/10^30)
theorem v2734_mg_checked : Scalar.distance (sourceCoefficient 33 95 3 2) v2734_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2734_upper : Scalar.QComplex := ((999993850497482881855061510840 : Int)/10^30,(-3506988340136744999066512242 : Int)/10^30)
theorem v2734_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 95 5) 1) 14) v2734_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2734 : Material (33 : Basis) (95 : Basis) where
  plus := ![v2734_pa,v2734_pb,v2734_pg]
  minus := ![(Primitive.Addresses.material2734 1).one,v2734_mb,v2734_mg]
  upper := v2734_upper
  lower := (Primitive.Addresses.material2734 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2734_pa_checked.trans (by decide +kernel)
    · exact v2734_pb_checked.trans (by decide +kernel)
    · exact v2734_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 95 Primitive.Addresses.material2734
    · exact v2734_mb_checked.trans (by decide +kernel)
    · exact v2734_mg_checked.trans (by decide +kernel)
  upper_error := v2734_upper_checked
  lower_error := reuse_lower_error 33 95 Primitive.Addresses.material2734

def v2735_pa : Scalar.QComplex := ((999998375768601255002850668062 : Int)/10^30,(-1802348512181358788588457441 : Int)/10^30)
theorem v2735_pa_checked : Scalar.distance (sourceCoefficient 33 96 1 0) v2735_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2735_pb : Scalar.QComplex := ((-777672683665359267790134 : Int)/10^30,(-431476717898339750933690444 : Int)/10^30)
theorem v2735_pb_checked : Scalar.distance (sourceCoefficient 33 96 1 1) v2735_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2735_pg : Scalar.QComplex := ((-93086267669871969048904 : Int)/10^30,(167774168543381909881 : Int)/10^30)
theorem v2735_pg_checked : Scalar.distance (sourceCoefficient 33 96 1 2) v2735_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2735_mb : Scalar.QComplex := ((-1150017368658557302995435 : Int)/10^30,(-431475886143337291487997501 : Int)/10^30)
theorem v2735_mb_checked : Scalar.distance (sourceCoefficient 33 96 3 1) v2735_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2735_mg : Scalar.QComplex := ((-93086088228049078069465 : Int)/10^30,(248103362622626015626 : Int)/10^30)
theorem v2735_mg_checked : Scalar.distance (sourceCoefficient 33 96 3 2) v2735_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2735_upper : Scalar.QComplex := ((999993775698464363317422203797 : Int)/10^30,(-3528252305227583724539746851 : Int)/10^30)
theorem v2735_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 96 5) 1) 14) v2735_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2735 : Material (33 : Basis) (96 : Basis) where
  plus := ![v2735_pa,v2735_pb,v2735_pg]
  minus := ![(Primitive.Addresses.material2735 1).one,v2735_mb,v2735_mg]
  upper := v2735_upper
  lower := (Primitive.Addresses.material2735 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2735_pa_checked.trans (by decide +kernel)
    · exact v2735_pb_checked.trans (by decide +kernel)
    · exact v2735_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 96 Primitive.Addresses.material2735
    · exact v2735_mb_checked.trans (by decide +kernel)
    · exact v2735_mg_checked.trans (by decide +kernel)
  upper_error := v2735_upper_checked
  lower_error := reuse_lower_error 33 96 Primitive.Addresses.material2735

def v2736_pa : Scalar.QComplex := ((999998241228425944229620212197 : Int)/10^30,(-1875510611762591721583671104 : Int)/10^30)
theorem v2736_pa_checked : Scalar.distance (sourceCoefficient 33 97 1 0) v2736_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2736_pb : Scalar.QComplex := ((-809240453282185845690841 : Int)/10^30,(-431476646913004065101069201 : Int)/10^30)
theorem v2736_pb_checked : Scalar.distance (sourceCoefficient 33 97 1 1) v2736_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2736_pg : Scalar.QComplex := ((-93086253750795089340815 : Int)/10^30,(174584563773209579497 : Int)/10^30)
theorem v2736_pg_checked : Scalar.distance (sourceCoefficient 33 97 1 2) v2736_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2736_mb : Scalar.QComplex := ((-1181585065264112898173647 : Int)/10^30,(-431475787916464616984051414 : Int)/10^30)
theorem v2736_mb_checked : Scalar.distance (sourceCoefficient 33 97 3 1) v2736_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2736_mg : Scalar.QComplex := ((-93086068431913026543396 : Int)/10^30,(254913743305095835502 : Int)/10^30)
theorem v2736_mg_checked : Scalar.distance (sourceCoefficient 33 97 3 2) v2736_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2736_upper : Scalar.QComplex := ((999993514887342770950015937842 : Int)/10^30,(-3601414063638326358182950255 : Int)/10^30)
theorem v2736_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 97 5) 1) 14) v2736_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2736 : Material (33 : Basis) (97 : Basis) where
  plus := ![v2736_pa,v2736_pb,v2736_pg]
  minus := ![(Primitive.Addresses.material2736 1).one,v2736_mb,v2736_mg]
  upper := v2736_upper
  lower := (Primitive.Addresses.material2736 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2736_pa_checked.trans (by decide +kernel)
    · exact v2736_pb_checked.trans (by decide +kernel)
    · exact v2736_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 97 Primitive.Addresses.material2736
    · exact v2736_mb_checked.trans (by decide +kernel)
    · exact v2736_mg_checked.trans (by decide +kernel)
  upper_error := v2736_upper_checked
  lower_error := reuse_lower_error 33 97 Primitive.Addresses.material2736

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
