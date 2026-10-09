import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B032

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v769_pa : Scalar.QComplex := ((999999986221652438329428291068 : Int)/10^30,(-166002093159990852832418669 : Int)/10^30)
theorem v769_pa_checked : Scalar.distance (sourceCoefficient 8 30 1 0) v769_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v769_pb : Scalar.QComplex := ((-71626169740122862429762 : Int)/10^30,(-431477503625211204151127624 : Int)/10^30)
theorem v769_pb_checked : Scalar.distance (sourceCoefficient 8 30 1 1) v769_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v769_pg : Scalar.QComplex := ((-93086427381409276144547 : Int)/10^30,(15452542003009920462 : Int)/10^30)
theorem v769_pg_checked : Scalar.distance (sourceCoefficient 8 30 1 2) v769_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v769_mb : Scalar.QComplex := ((-443971795673608191248733 : Int)/10^30,(-431477281156258545613629694 : Int)/10^30)
theorem v769_mb_checked : Scalar.distance (sourceCoefficient 8 30 3 1) v769_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v769_mg : Scalar.QComplex := ((-93086379386230310208969 : Int)/10^30,(95781930622420584828 : Int)/10^30)
theorem v769_mg_checked : Scalar.distance (sourceCoefficient 8 30 3 2) v769_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v769_upper : Scalar.QComplex := ((999998210334588009362408413825 : Int)/10^30,(-1891911102847855350984378343 : Int)/10^30)
theorem v769_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 30 5) 1) 14) v769_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material769 : Material (8 : Basis) (30 : Basis) where
  plus := ![v769_pa,v769_pb,v769_pg]
  minus := ![(Primitive.Addresses.material769 1).one,v769_mb,v769_mg]
  upper := v769_upper
  lower := (Primitive.Addresses.material769 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v769_pa_checked.trans (by decide +kernel)
    · exact v769_pb_checked.trans (by decide +kernel)
    · exact v769_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 30 Primitive.Addresses.material769
    · exact v769_mb_checked.trans (by decide +kernel)
    · exact v769_mg_checked.trans (by decide +kernel)
  upper_error := v769_upper_checked
  lower_error := reuse_lower_error 8 30 Primitive.Addresses.material769

def v770_pa : Scalar.QComplex := ((999999984318297396896308753108 : Int)/10^30,(-177097162485149902419735843 : Int)/10^30)
theorem v770_pa_checked : Scalar.distance (sourceCoefficient 8 31 1 0) v770_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v770_pb : Scalar.QComplex := ((-76413442506814774213182 : Int)/10^30,(-431477502158903178094108771 : Int)/10^30)
theorem v770_pb_checked : Scalar.distance (sourceCoefficient 8 31 1 1) v770_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v770_pg : Scalar.QComplex := ((-93086427134651268208144 : Int)/10^30,(16485342369945638856 : Int)/10^30)
theorem v770_pg_checked : Scalar.distance (sourceCoefficient 8 31 1 2) v770_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v770_mb : Scalar.QComplex := ((-448759065392421876393676 : Int)/10^30,(-431477275558750278636546771 : Int)/10^30)
theorem v770_mb_checked : Scalar.distance (sourceCoefficient 8 31 3 1) v770_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v770_mg : Scalar.QComplex := ((-93086378248212193088111 : Int)/10^30,(96814730391856478022 : Int)/10^30)
theorem v770_mg_checked : Scalar.distance (sourceCoefficient 8 31 3 2) v770_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v770_upper : Scalar.QComplex := ((999998189282152684355063942446 : Int)/10^30,(-1903006152363193828650310717 : Int)/10^30)
theorem v770_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 31 5) 1) 14) v770_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material770 : Material (8 : Basis) (31 : Basis) where
  plus := ![v770_pa,v770_pb,v770_pg]
  minus := ![(Primitive.Addresses.material770 1).one,v770_mb,v770_mg]
  upper := v770_upper
  lower := (Primitive.Addresses.material770 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v770_pa_checked.trans (by decide +kernel)
    · exact v770_pb_checked.trans (by decide +kernel)
    · exact v770_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 31 Primitive.Addresses.material770
    · exact v770_mb_checked.trans (by decide +kernel)
    · exact v770_mg_checked.trans (by decide +kernel)
  upper_error := v770_upper_checked
  lower_error := reuse_lower_error 8 31 Primitive.Addresses.material770

def v771_pa : Scalar.QComplex := ((999999983461059880291510211182 : Int)/10^30,(-181873252475124662829995296 : Int)/10^30)
theorem v771_pa_checked : Scalar.distance (sourceCoefficient 8 32 1 0) v771_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v771_pb : Scalar.QComplex := ((-78474217866598479106354 : Int)/10^30,(-431477501505897560175616404 : Int)/10^30)
theorem v771_pb_checked : Scalar.distance (sourceCoefficient 8 32 1 1) v771_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v771_pg : Scalar.QComplex := ((-93086427024313363739029 : Int)/10^30,(16929931524203335494 : Int)/10^30)
theorem v771_pg_checked : Scalar.distance (sourceCoefficient 8 32 1 2) v771_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v771_mb : Scalar.QComplex := ((-450819839421370294770354 : Int)/10^30,(-431477273127388582245344061 : Int)/10^30)
theorem v771_mb_checked : Scalar.distance (sourceCoefficient 8 32 3 1) v771_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v771_mg : Scalar.QComplex := ((-93086377754213913130647 : Int)/10^30,(97259319285356671679 : Int)/10^30)
theorem v771_mg_checked : Scalar.distance (sourceCoefficient 8 32 3 2) v771_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v771_upper : Scalar.QComplex := ((999998180181818405307677279671 : Int)/10^30,(-1907782233760229402254357041 : Int)/10^30)
theorem v771_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 32 5) 1) 14) v771_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material771 : Material (8 : Basis) (32 : Basis) where
  plus := ![v771_pa,v771_pb,v771_pg]
  minus := ![(Primitive.Addresses.material771 1).one,v771_mb,v771_mg]
  upper := v771_upper
  lower := (Primitive.Addresses.material771 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v771_pa_checked.trans (by decide +kernel)
    · exact v771_pb_checked.trans (by decide +kernel)
    · exact v771_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 32 Primitive.Addresses.material771
    · exact v771_mb_checked.trans (by decide +kernel)
    · exact v771_mg_checked.trans (by decide +kernel)
  upper_error := v771_upper_checked
  lower_error := reuse_lower_error 8 32 Primitive.Addresses.material771

def v772_pa : Scalar.QComplex := ((999999982228338175138747569994 : Int)/10^30,(-188529369950388740068245279 : Int)/10^30)
theorem v772_pa_checked : Scalar.distance (sourceCoefficient 8 33 1 0) v772_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v772_pb : Scalar.QComplex := ((-81346182776633774118500 : Int)/10^30,(-431477500573958664925736502 : Int)/10^30)
theorem v772_pb_checked : Scalar.distance (sourceCoefficient 8 33 1 1) v772_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v772_pg : Scalar.QComplex := ((-93086426866410856854422 : Int)/10^30,(17549525719941614366 : Int)/10^30)
theorem v772_pg_checked : Scalar.distance (sourceCoefficient 8 33 1 2) v772_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v772_mb : Scalar.QComplex := ((-453691802457820504864915 : Int)/10^30,(-431477269717073665136353022 : Int)/10^30)
theorem v772_mb_checked : Scalar.distance (sourceCoefficient 8 33 3 1) v772_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v772_mg : Scalar.QComplex := ((-93086377061629579604901 : Int)/10^30,(97878913114128962848 : Int)/10^30)
theorem v772_mg_checked : Scalar.distance (sourceCoefficient 8 33 3 2) v772_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v772_upper : Scalar.QComplex := ((999998167461243612103721810669 : Int)/10^30,(-1914438339194422551115499582 : Int)/10^30)
theorem v772_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 33 5) 1) 14) v772_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material772 : Material (8 : Basis) (33 : Basis) where
  plus := ![v772_pa,v772_pb,v772_pg]
  minus := ![(Primitive.Addresses.material772 1).one,v772_mb,v772_mg]
  upper := v772_upper
  lower := (Primitive.Addresses.material772 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v772_pa_checked.trans (by decide +kernel)
    · exact v772_pb_checked.trans (by decide +kernel)
    · exact v772_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 33 Primitive.Addresses.material772
    · exact v772_mb_checked.trans (by decide +kernel)
    · exact v772_mg_checked.trans (by decide +kernel)
  upper_error := v772_upper_checked
  lower_error := reuse_lower_error 8 33 Primitive.Addresses.material772

def v773_pa : Scalar.QComplex := ((999999979049705027864147545105 : Int)/10^30,(-204696334860585243186822824 : Int)/10^30)
theorem v773_pa_checked : Scalar.distance (sourceCoefficient 8 34 1 0) v773_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v773_pb : Scalar.QComplex := ((-88321864307592937154147 : Int)/10^30,(-431477498204245610472805262 : Int)/10^30)
theorem v773_pb_checked : Scalar.distance (sourceCoefficient 8 34 1 1) v773_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v773_pg : Scalar.QComplex := ((-93086426462847560927138 : Int)/10^30,(19054450721410651023 : Int)/10^30)
theorem v773_pg_checked : Scalar.distance (sourceCoefficient 8 34 1 2) v773_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v773_mb : Scalar.QComplex := ((-460667479346458991450410 : Int)/10^30,(-431477261327662504851638681 : Int)/10^30)
theorem v773_mb_checked : Scalar.distance (sourceCoefficient 8 34 3 1) v773_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v773_mg : Scalar.QComplex := ((-93086375359383936980878 : Int)/10^30,(99383837206988694419 : Int)/10^30)
theorem v773_mg_checked : Scalar.distance (sourceCoefficient 8 34 3 2) v773_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v773_upper : Scalar.QComplex := ((999998136379900419630410006823 : Int)/10^30,(-1930605274539791476750185078 : Int)/10^30)
theorem v773_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 34 5) 1) 14) v773_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material773 : Material (8 : Basis) (34 : Basis) where
  plus := ![v773_pa,v773_pb,v773_pg]
  minus := ![(Primitive.Addresses.material773 1).one,v773_mb,v773_mg]
  upper := v773_upper
  lower := (Primitive.Addresses.material773 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v773_pa_checked.trans (by decide +kernel)
    · exact v773_pb_checked.trans (by decide +kernel)
    · exact v773_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 34 Primitive.Addresses.material773
    · exact v773_mb_checked.trans (by decide +kernel)
    · exact v773_mg_checked.trans (by decide +kernel)
  upper_error := v773_upper_checked
  lower_error := reuse_lower_error 8 34 Primitive.Addresses.material773

def v774_pa : Scalar.QComplex := ((999999967217037732672663228347 : Int)/10^30,(-256058437587852313526242582 : Int)/10^30)
theorem v774_pa_checked : Scalar.distance (sourceCoefficient 8 35 1 0) v774_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v774_pb : Scalar.QComplex := ((-110483455483256568759549 : Int)/10^30,(-431477489678016647216711248 : Int)/10^30)
theorem v774_pb_checked : Scalar.distance (sourceCoefficient 8 35 1 1) v774_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v774_pg : Scalar.QComplex := ((-93086424992398107438344 : Int)/10^30,(23835565325592705251 : Int)/10^30)
theorem v774_pg_checked : Scalar.distance (sourceCoefficient 8 35 1 2) v774_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v774_mb : Scalar.QComplex := ((-482829054912597805411944 : Int)/10^30,(-431477233676981652717099710 : Int)/10^30)
theorem v774_mb_checked : Scalar.distance (sourceCoefficient 8 35 3 1) v774_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v774_mg : Scalar.QComplex := ((-93086369763048461006726 : Int)/10^30,(104164948762011622002 : Int)/10^30)
theorem v774_mg_checked : Scalar.distance (sourceCoefficient 8 35 3 2) v774_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v774_upper : Scalar.QComplex := ((999998035900920974105074699874 : Int)/10^30,(-1981967280347129650927212503 : Int)/10^30)
theorem v774_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 35 5) 1) 14) v774_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material774 : Material (8 : Basis) (35 : Basis) where
  plus := ![v774_pa,v774_pb,v774_pg]
  minus := ![(Primitive.Addresses.material774 1).one,v774_mb,v774_mg]
  upper := v774_upper
  lower := (Primitive.Addresses.material774 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v774_pa_checked.trans (by decide +kernel)
    · exact v774_pb_checked.trans (by decide +kernel)
    · exact v774_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 35 Primitive.Addresses.material774
    · exact v774_mb_checked.trans (by decide +kernel)
    · exact v774_mg_checked.trans (by decide +kernel)
  upper_error := v774_upper_checked
  lower_error := reuse_lower_error 8 35 Primitive.Addresses.material774

def v775_pa : Scalar.QComplex := ((999999962952664347776188857801 : Int)/10^30,(-272203361353129773131575026 : Int)/10^30)
theorem v775_pa_checked : Scalar.distance (sourceCoefficient 8 36 1 0) v775_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v775_pb : Scalar.QComplex := ((-117449626574892773891041 : Int)/10^30,(-431477486684411251477511303 : Int)/10^30)
theorem v775_pb_checked : Scalar.distance (sourceCoefficient 8 36 1 1) v775_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v775_pg : Scalar.QComplex := ((-93086424471002086717188 : Int)/10^30,(25338438576072641829 : Int)/10^30)
theorem v775_pg_checked : Scalar.distance (sourceCoefficient 8 36 1 2) v775_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v775_mb : Scalar.QComplex := ((-489795220827063513839687 : Int)/10^30,(-431477224671885464251174696 : Int)/10^30)
theorem v775_mb_checked : Scalar.distance (sourceCoefficient 8 36 3 1) v775_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v775_mg : Scalar.QComplex := ((-93086367944740706159497 : Int)/10^30,(105667821002961879648 : Int)/10^30)
theorem v775_mg_checked : Scalar.distance (sourceCoefficient 8 36 3 2) v775_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v775_upper : Scalar.QComplex := ((999998003771880177665654211349 : Int)/10^30,(-1998112172706518076720390249 : Int)/10^30)
theorem v775_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 36 5) 1) 14) v775_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material775 : Material (8 : Basis) (36 : Basis) where
  plus := ![v775_pa,v775_pb,v775_pg]
  minus := ![(Primitive.Addresses.material775 1).one,v775_mb,v775_mg]
  upper := v775_upper
  lower := (Primitive.Addresses.material775 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v775_pa_checked.trans (by decide +kernel)
    · exact v775_pb_checked.trans (by decide +kernel)
    · exact v775_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 36 Primitive.Addresses.material775
    · exact v775_mb_checked.trans (by decide +kernel)
    · exact v775_mg_checked.trans (by decide +kernel)
  upper_error := v775_upper_checked
  lower_error := reuse_lower_error 8 36 Primitive.Addresses.material775

def v776_pa : Scalar.QComplex := ((999999961052314896720271249582 : Int)/10^30,(-279097417920046839326555800 : Int)/10^30)
theorem v776_pa_checked : Scalar.distance (sourceCoefficient 8 37 1 0) v776_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v776_pb : Scalar.QComplex := ((-120424256744974387023196 : Int)/10^30,(-431477485360421160318362674 : Int)/10^30)
theorem v776_pb_checked : Scalar.distance (sourceCoefficient 8 37 1 1) v776_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v776_pg : Scalar.QComplex := ((-93086424239735716539330 : Int)/10^30,(25980181660588231897 : Int)/10^30)
theorem v776_pg_checked : Scalar.distance (sourceCoefficient 8 37 1 2) v776_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v776_mb : Scalar.QComplex := ((-492769848747010548965531 : Int)/10^30,(-431477220780924001663186554 : Int)/10^30)
theorem v776_mb_checked : Scalar.distance (sourceCoefficient 8 37 3 1) v776_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v776_mg : Scalar.QComplex := ((-93086367159679043191319 : Int)/10^30,(106309563648954728631 : Int)/10^30)
theorem v776_mg_checked : Scalar.distance (sourceCoefficient 8 37 3 2) v776_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v776_upper : Scalar.QComplex := ((999997989973017346384364086247 : Int)/10^30,(-2005006215725716965097384453 : Int)/10^30)
theorem v776_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 37 5) 1) 14) v776_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material776 : Material (8 : Basis) (37 : Basis) where
  plus := ![v776_pa,v776_pb,v776_pg]
  minus := ![(Primitive.Addresses.material776 1).one,v776_mb,v776_mg]
  upper := v776_upper
  lower := (Primitive.Addresses.material776 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v776_pa_checked.trans (by decide +kernel)
    · exact v776_pb_checked.trans (by decide +kernel)
    · exact v776_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 37 Primitive.Addresses.material776
    · exact v776_mb_checked.trans (by decide +kernel)
    · exact v776_mg_checked.trans (by decide +kernel)
  upper_error := v776_upper_checked
  lower_error := reuse_lower_error 8 37 Primitive.Addresses.material776

def v777_pa : Scalar.QComplex := ((999999954277592831000116356657 : Int)/10^30,(-302398432944784371544387597 : Int)/10^30)
theorem v777_pa_checked : Scalar.distance (sourceCoefficient 8 38 1 0) v777_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v777_pb : Scalar.QComplex := ((-130478119975313287565923 : Int)/10^30,(-431477480683121991142708860 : Int)/10^30)
theorem v777_pb_checked : Scalar.distance (sourceCoefficient 8 38 1 1) v777_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v777_pg : Scalar.QComplex := ((-93086423419880985144338 : Int)/10^30,(28149189857655405734 : Int)/10^30)
theorem v777_pg_checked : Scalar.distance (sourceCoefficient 8 38 1 2) v777_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v777_mb : Scalar.QComplex := ((-502823704197538159340484 : Int)/10^30,(-431477207427595415468132571 : Int)/10^30)
theorem v777_mb_checked : Scalar.distance (sourceCoefficient 8 38 3 1) v777_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v777_mg : Scalar.QComplex := ((-93086364468068231499571 : Int)/10^30,(108478570330903313820 : Int)/10^30)
theorem v777_mg_checked : Scalar.distance (sourceCoefficient 8 38 3 2) v777_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v777_upper : Scalar.QComplex := ((999997942982867289690472618148 : Int)/10^30,(-2028307184353774060018166845 : Int)/10^30)
theorem v777_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 38 5) 1) 14) v777_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material777 : Material (8 : Basis) (38 : Basis) where
  plus := ![v777_pa,v777_pb,v777_pg]
  minus := ![(Primitive.Addresses.material777 1).one,v777_mb,v777_mg]
  upper := v777_upper
  lower := (Primitive.Addresses.material777 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v777_pa_checked.trans (by decide +kernel)
    · exact v777_pb_checked.trans (by decide +kernel)
    · exact v777_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 38 Primitive.Addresses.material777
    · exact v777_mb_checked.trans (by decide +kernel)
    · exact v777_mg_checked.trans (by decide +kernel)
  upper_error := v777_upper_checked
  lower_error := reuse_lower_error 8 38 Primitive.Addresses.material777

def v778_pa : Scalar.QComplex := ((999999950098594199117660312216 : Int)/10^30,(-315915825991061072184389805 : Int)/10^30)
theorem v778_pa_checked : Scalar.distance (sourceCoefficient 8 39 1 0) v778_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v778_pb : Scalar.QComplex := ((-136310570606207961441986 : Int)/10^30,(-431477477826564499811197104 : Int)/10^30)
theorem v778_pb_checked : Scalar.distance (sourceCoefficient 8 39 1 1) v778_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v778_pg : Scalar.QComplex := ((-93086422917241852916261 : Int)/10^30,(29407475651928072877 : Int)/10^30)
theorem v778_pg_checked : Scalar.distance (sourceCoefficient 8 39 1 2) v778_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v778_mb : Scalar.QComplex := ((-508656150191664446726919 : Int)/10^30,(-431477199537896777126555955 : Int)/10^30)
theorem v778_mb_checked : Scalar.distance (sourceCoefficient 8 39 3 1) v778_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v778_mg : Scalar.QComplex := ((-93086362879585317058147 : Int)/10^30,(109736855222903740167 : Int)/10^30)
theorem v778_mg_checked : Scalar.distance (sourceCoefficient 8 39 3 2) v778_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v778_upper : Scalar.QComplex := ((999997915474080772379913370760 : Int)/10^30,(-2041824550054909159922913793 : Int)/10^30)
theorem v778_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 39 5) 1) 14) v778_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material778 : Material (8 : Basis) (39 : Basis) where
  plus := ![v778_pa,v778_pb,v778_pg]
  minus := ![(Primitive.Addresses.material778 1).one,v778_mb,v778_mg]
  upper := v778_upper
  lower := (Primitive.Addresses.material778 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v778_pa_checked.trans (by decide +kernel)
    · exact v778_pb_checked.trans (by decide +kernel)
    · exact v778_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 39 Primitive.Addresses.material778
    · exact v778_mb_checked.trans (by decide +kernel)
    · exact v778_mg_checked.trans (by decide +kernel)
  upper_error := v778_upper_checked
  lower_error := reuse_lower_error 8 39 Primitive.Addresses.material778

def v779_pa : Scalar.QComplex := ((999999942657638928474610075340 : Int)/10^30,(-338651323421161912033563917 : Int)/10^30)
theorem v779_pa_checked : Scalar.distance (sourceCoefficient 8 40 1 0) v779_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v779_pb : Scalar.QComplex := ((-146120425563916477751283 : Int)/10^30,(-431477472784904483313460236 : Int)/10^30)
theorem v779_pb_checked : Scalar.distance (sourceCoefficient 8 40 1 1) v779_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v779_pg : Scalar.QComplex := ((-93086422027075105382222 : Int)/10^30,(31523841819661301728 : Int)/10^30)
theorem v779_pg_checked : Scalar.distance (sourceCoefficient 8 40 1 2) v779_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v779_mb : Scalar.QComplex := ((-518465997145990103462130 : Int)/10^30,(-431477186030775628832994565 : Int)/10^30)
theorem v779_mb_checked : Scalar.distance (sourceCoefficient 8 40 3 1) v779_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v779_mg : Scalar.QComplex := ((-93086360163090215813934 : Int)/10^30,(111853219834443310559 : Int)/10^30)
theorem v779_mg_checked : Scalar.distance (sourceCoefficient 8 40 3 2) v779_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v779_upper : Scalar.QComplex := ((999997868793730568026729448662 : Int)/10^30,(-2064560000780743517830547539 : Int)/10^30)
theorem v779_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 40 5) 1) 14) v779_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material779 : Material (8 : Basis) (40 : Basis) where
  plus := ![v779_pa,v779_pb,v779_pg]
  minus := ![(Primitive.Addresses.material779 1).one,v779_mb,v779_mg]
  upper := v779_upper
  lower := (Primitive.Addresses.material779 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v779_pa_checked.trans (by decide +kernel)
    · exact v779_pb_checked.trans (by decide +kernel)
    · exact v779_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 40 Primitive.Addresses.material779
    · exact v779_mb_checked.trans (by decide +kernel)
    · exact v779_mg_checked.trans (by decide +kernel)
  upper_error := v779_upper_checked
  lower_error := reuse_lower_error 8 40 Primitive.Addresses.material779

def v780_pa : Scalar.QComplex := ((999999937647722030707149122152 : Int)/10^30,(-353135316912340465210463084 : Int)/10^30)
theorem v780_pa_checked : Scalar.distance (sourceCoefficient 8 41 1 0) v780_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v780_pb : Scalar.QComplex := ((-152369942404062265353097 : Int)/10^30,(-431477469417969250159170303 : Int)/10^30)
theorem v780_pb_checked : Scalar.distance (sourceCoefficient 8 41 1 1) v780_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v780_pg : Scalar.QComplex := ((-93086421430708232247885 : Int)/10^30,(32872104981819459994 : Int)/10^30)
theorem v780_pg_checked : Scalar.distance (sourceCoefficient 8 41 1 2) v780_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v780_mb : Scalar.QComplex := ((-524715508753641689369871 : Int)/10^30,(-431477177270790084086658442 : Int)/10^30)
theorem v780_mb_checked : Scalar.distance (sourceCoefficient 8 41 3 1) v780_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v780_mg : Scalar.QComplex := ((-93086358403233179310408 : Int)/10^30,(113201481979943722735 : Int)/10^30)
theorem v780_mg_checked : Scalar.distance (sourceCoefficient 8 41 3 2) v780_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v780_upper : Scalar.QComplex := ((999997838785762343793088551669 : Int)/10^30,(-2079043964053053105853955855 : Int)/10^30)
theorem v780_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 41 5) 1) 14) v780_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material780 : Material (8 : Basis) (41 : Basis) where
  plus := ![v780_pa,v780_pb,v780_pg]
  minus := ![(Primitive.Addresses.material780 1).one,v780_mb,v780_mg]
  upper := v780_upper
  lower := (Primitive.Addresses.material780 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v780_pa_checked.trans (by decide +kernel)
    · exact v780_pb_checked.trans (by decide +kernel)
    · exact v780_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 41 Primitive.Addresses.material780
    · exact v780_mb_checked.trans (by decide +kernel)
    · exact v780_mg_checked.trans (by decide +kernel)
  upper_error := v780_upper_checked
  lower_error := reuse_lower_error 8 41 Primitive.Addresses.material780

def v781_pa : Scalar.QComplex := ((999999933453558771091894013073 : Int)/10^30,(-364818966104268449314202625 : Int)/10^30)
theorem v781_pa_checked : Scalar.distance (sourceCoefficient 8 42 1 0) v781_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v781_pb : Scalar.QComplex := ((-157411173742581825772875 : Int)/10^30,(-431477466614054591615837987 : Int)/10^30)
theorem v781_pb_checked : Scalar.distance (sourceCoefficient 8 42 1 1) v781_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v781_pg : Scalar.QComplex := ((-93086420933041839304621 : Int)/10^30,(33959694103035843592 : Int)/10^30)
theorem v781_pg_checked : Scalar.distance (sourceCoefficient 8 42 1 2) v781_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v781_mb : Scalar.QComplex := ((-529756735795428360110326 : Int)/10^30,(-431477170116520873057563644 : Int)/10^30)
theorem v781_mb_checked : Scalar.distance (sourceCoefficient 8 42 3 1) v781_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v781_mg : Scalar.QComplex := ((-93086356967026543257026 : Int)/10^30,(114289070266737288178 : Int)/10^30)
theorem v781_mg_checked : Scalar.distance (sourceCoefficient 8 42 3 2) v781_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v781_upper : Scalar.QComplex := ((999997814426686757998581423267 : Int)/10^30,(-2090727588604812781847697480 : Int)/10^30)
theorem v781_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 42 5) 1) 14) v781_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material781 : Material (8 : Basis) (42 : Basis) where
  plus := ![v781_pa,v781_pb,v781_pg]
  minus := ![(Primitive.Addresses.material781 1).one,v781_mb,v781_mg]
  upper := v781_upper
  lower := (Primitive.Addresses.material781 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v781_pa_checked.trans (by decide +kernel)
    · exact v781_pb_checked.trans (by decide +kernel)
    · exact v781_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 42 Primitive.Addresses.material781
    · exact v781_mb_checked.trans (by decide +kernel)
    · exact v781_mg_checked.trans (by decide +kernel)
  upper_error := v781_upper_checked
  lower_error := reuse_lower_error 8 42 Primitive.Addresses.material781

def v782_pa : Scalar.QComplex := ((999999927687187013974581857416 : Int)/10^30,(-380296753526647811079160503 : Int)/10^30)
theorem v782_pa_checked : Scalar.distance (sourceCoefficient 8 43 1 0) v782_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v782_pb : Scalar.QComplex := ((-164089490180416072557708 : Int)/10^30,(-431477462778670621115319575 : Int)/10^30)
theorem v782_pb_checked : Scalar.distance (sourceCoefficient 8 43 1 1) v782_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v782_pg : Scalar.QComplex := ((-93086420250935847543012 : Int)/10^30,(35400465978755383438 : Int)/10^30)
theorem v782_pg_checked : Scalar.distance (sourceCoefficient 8 43 1 2) v782_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v782_mb : Scalar.QComplex := ((-536435046436856555690076 : Int)/10^30,(-431477160518052025001702117 : Int)/10^30)
theorem v782_mb_checked : Scalar.distance (sourceCoefficient 8 43 3 1) v782_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v782_mg : Scalar.QComplex := ((-93086355041599566685143 : Int)/10^30,(115729841017364862190 : Int)/10^30)
theorem v782_mg_checked : Scalar.distance (sourceCoefficient 8 43 3 2) v782_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v782_upper : Scalar.QComplex := ((999997781947066632094323590188 : Int)/10^30,(-2106205343022611394982130581 : Int)/10^30)
theorem v782_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 43 5) 1) 14) v782_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material782 : Material (8 : Basis) (43 : Basis) where
  plus := ![v782_pa,v782_pb,v782_pg]
  minus := ![(Primitive.Addresses.material782 1).one,v782_mb,v782_mg]
  upper := v782_upper
  lower := (Primitive.Addresses.material782 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v782_pa_checked.trans (by decide +kernel)
    · exact v782_pb_checked.trans (by decide +kernel)
    · exact v782_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 43 Primitive.Addresses.material782
    · exact v782_mb_checked.trans (by decide +kernel)
    · exact v782_mg_checked.trans (by decide +kernel)
  upper_error := v782_upper_checked
  lower_error := reuse_lower_error 8 43 Primitive.Addresses.material782

def v783_pa : Scalar.QComplex := ((999999925443108034015303949449 : Int)/10^30,(-386152532522110040445092215 : Int)/10^30)
theorem v783_pa_checked : Scalar.distance (sourceCoefficient 8 44 1 0) v783_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v783_pb : Scalar.QComplex := ((-166616126826372827259241 : Int)/10^30,(-431477461291678245187355404 : Int)/10^30)
theorem v783_pb_checked : Scalar.distance (sourceCoefficient 8 44 1 1) v783_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v783_pg : Scalar.QComplex := ((-93086419986088243537062 : Int)/10^30,(35945559501033930897 : Int)/10^30)
theorem v783_pg_checked : Scalar.distance (sourceCoefficient 8 44 1 2) v783_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v783_mb : Scalar.QComplex := ((-538961680858823565327382 : Int)/10^30,(-431477156850686572778525836 : Int)/10^30)
theorem v783_mb_checked : Scalar.distance (sourceCoefficient 8 44 3 1) v783_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v783_mg : Scalar.QComplex := ((-93086354306360901668574 : Int)/10^30,(116274934108128625335 : Int)/10^30)
theorem v783_mg_checked : Scalar.distance (sourceCoefficient 8 44 3 2) v783_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v783_upper : Scalar.QComplex := ((999997769596447680379981150004 : Int)/10^30,(-2112061109423501940573037436 : Int)/10^30)
theorem v783_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 44 5) 1) 14) v783_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material783 : Material (8 : Basis) (44 : Basis) where
  plus := ![v783_pa,v783_pb,v783_pg]
  minus := ![(Primitive.Addresses.material783 1).one,v783_mb,v783_mg]
  upper := v783_upper
  lower := (Primitive.Addresses.material783 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v783_pa_checked.trans (by decide +kernel)
    · exact v783_pb_checked.trans (by decide +kernel)
    · exact v783_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 44 Primitive.Addresses.material783
    · exact v783_mb_checked.trans (by decide +kernel)
    · exact v783_mg_checked.trans (by decide +kernel)
  upper_error := v783_upper_checked
  lower_error := reuse_lower_error 8 44 Primitive.Addresses.material783

def v784_pa : Scalar.QComplex := ((999999924313877082513398383160 : Int)/10^30,(-389065855744993383443755271 : Int)/10^30)
theorem v784_pa_checked : Scalar.distance (sourceCoefficient 8 45 1 0) v784_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v784_pb : Scalar.QComplex := ((-167873160127103691811626 : Int)/10^30,(-431477460544532253219585165 : Int)/10^30)
theorem v784_pb_checked : Scalar.distance (sourceCoefficient 8 45 1 1) v784_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v784_pg : Scalar.QComplex := ((-93086419852936025675158 : Int)/10^30,(36216750339425713830 : Int)/10^30)
theorem v784_pg_checked : Scalar.distance (sourceCoefficient 8 45 1 2) v784_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v784_mb : Scalar.QComplex := ((-540218713046750141895909 : Int)/10^30,(-431477155018777735154847831 : Int)/10^30)
theorem v784_mb_checked : Scalar.distance (sourceCoefficient 8 45 3 1) v784_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v784_mg : Scalar.QComplex := ((-93086353939183253835175 : Int)/10^30,(116546124730639298040 : Int)/10^30)
theorem v784_mg_checked : Scalar.distance (sourceCoefficient 8 45 3 2) v784_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v784_upper : Scalar.QComplex := ((999997763439086822656502763317 : Int)/10^30,(-2114974426358382386811964741 : Int)/10^30)
theorem v784_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 45 5) 1) 14) v784_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material784 : Material (8 : Basis) (45 : Basis) where
  plus := ![v784_pa,v784_pb,v784_pg]
  minus := ![(Primitive.Addresses.material784 1).one,v784_mb,v784_mg]
  upper := v784_upper
  lower := (Primitive.Addresses.material784 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v784_pa_checked.trans (by decide +kernel)
    · exact v784_pb_checked.trans (by decide +kernel)
    · exact v784_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 45 Primitive.Addresses.material784
    · exact v784_mb_checked.trans (by decide +kernel)
    · exact v784_mg_checked.trans (by decide +kernel)
  upper_error := v784_upper_checked
  lower_error := reuse_lower_error 8 45 Primitive.Addresses.material784

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
