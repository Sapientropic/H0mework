import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B070

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1681_pa : Scalar.QComplex := ((999999927855679103966259852931 : Int)/10^30,(-379853440931189200072973809 : Int)/10^30)
theorem v1681_pa_checked : Scalar.distance (sourceCoefficient 19 29 1 0) v1681_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1681_pb : Scalar.QComplex := ((-163898220205734205665152 : Int)/10^30,(-431477487684779783084698030 : Int)/10^30)
theorem v1681_pb_checked : Scalar.distance (sourceCoefficient 19 29 1 1) v1681_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1681_pg : Scalar.QComplex := ((-93086422945384689090076 : Int)/10^30,(35359200610745893483 : Int)/10^30)
theorem v1681_pg_checked : Scalar.distance (sourceCoefficient 19 29 1 2) v1681_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1681_mb : Scalar.QComplex := ((-536243798026243719104736 : Int)/10^30,(-431477185589209286958950133 : Int)/10^30)
theorem v1681_mb_checked : Scalar.distance (sourceCoefficient 19 29 3 1) v1681_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1681_mg : Scalar.QComplex := ((-93086357771657559034766 : Int)/10^30,(115688577989908351449 : Int)/10^30)
theorem v1681_mg_checked : Scalar.distance (sourceCoefficient 19 29 3 2) v1681_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1681_upper : Scalar.QComplex := ((999997782880675793893886604507 : Int)/10^30,(-2105762031378216881598638068 : Int)/10^30)
theorem v1681_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 29 5) 1) 14) v1681_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1681 : Material (19 : Basis) (29 : Basis) where
  plus := ![v1681_pa,v1681_pb,v1681_pg]
  minus := ![(Primitive.Addresses.material1681 1).one,v1681_mb,v1681_mg]
  upper := v1681_upper
  lower := (Primitive.Addresses.material1681 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1681_pa_checked.trans (by decide +kernel)
    · exact v1681_pb_checked.trans (by decide +kernel)
    · exact v1681_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 29 Primitive.Addresses.material1681
    · exact v1681_mb_checked.trans (by decide +kernel)
    · exact v1681_mg_checked.trans (by decide +kernel)
  upper_error := v1681_upper_checked
  lower_error := reuse_lower_error 19 29 Primitive.Addresses.material1681

def v1682_pa : Scalar.QComplex := ((999999925860645627483195170666 : Int)/10^30,(-385069738162309689029233360 : Int)/10^30)
theorem v1682_pa_checked : Scalar.distance (sourceCoefficient 19 30 1 0) v1682_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1682_pb : Scalar.QComplex := ((-166148935141275268235299 : Int)/10^30,(-431477486691170497776229839 : Int)/10^30)
theorem v1682_pb_checked : Scalar.distance (sourceCoefficient 19 30 1 1) v1682_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1682_pg : Scalar.QComplex := ((-93086422745349394477540 : Int)/10^30,(35844767090525650103 : Int)/10^30)
theorem v1682_pg_checked : Scalar.distance (sourceCoefficient 19 30 1 2) v1682_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1682_mb : Scalar.QComplex := ((-538494511266300685698653 : Int)/10^30,(-431477182653334750682415533 : Int)/10^30)
theorem v1682_mb_checked : Scalar.distance (sourceCoefficient 19 30 3 1) v1682_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1682_mg : Scalar.QComplex := ((-93086357152600335957013 : Int)/10^30,(116174144116268066168 : Int)/10^30)
theorem v1682_mg_checked : Scalar.distance (sourceCoefficient 19 30 3 2) v1682_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1682_upper : Scalar.QComplex := ((999997771882789486653093050343 : Int)/10^30,(-2110978317397028601730404591 : Int)/10^30)
theorem v1682_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 30 5) 1) 14) v1682_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1682 : Material (19 : Basis) (30 : Basis) where
  plus := ![v1682_pa,v1682_pb,v1682_pg]
  minus := ![(Primitive.Addresses.material1682 1).one,v1682_mb,v1682_mg]
  upper := v1682_upper
  lower := (Primitive.Addresses.material1682 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1682_pa_checked.trans (by decide +kernel)
    · exact v1682_pb_checked.trans (by decide +kernel)
    · exact v1682_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 30 Primitive.Addresses.material1682
    · exact v1682_mb_checked.trans (by decide +kernel)
    · exact v1682_mg_checked.trans (by decide +kernel)
  upper_error := v1682_upper_checked
  lower_error := reuse_lower_error 19 30 Primitive.Addresses.material1682

def v1683_pa : Scalar.QComplex := ((999999921526719845837685956426 : Int)/10^30,(-396164806804275498019180647 : Int)/10^30)
theorem v1683_pa_checked : Scalar.distance (sourceCoefficient 19 31 1 0) v1683_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1683_pb : Scalar.QComplex := ((-170936207711445498981176 : Int)/10^30,(-431477484525704724007862318 : Int)/10^30)
theorem v1683_pb_checked : Scalar.distance (sourceCoefficient 19 31 1 1) v1683_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1683_pg : Scalar.QComplex := ((-93086422310047093670607 : Int)/10^30,(36877567404464685712 : Int)/10^30)
theorem v1683_pg_checked : Scalar.distance (sourceCoefficient 19 31 1 2) v1683_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1683_mb : Scalar.QComplex := ((-543281780185251115601196 : Int)/10^30,(-431477176356669165911726230 : Int)/10^30)
theorem v1683_mb_checked : Scalar.distance (sourceCoefficient 19 31 3 1) v1683_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1683_mg : Scalar.QComplex := ((-93086355826038041903033 : Int)/10^30,(117206943670002063282 : Int)/10^30)
theorem v1683_mg_checked : Scalar.distance (sourceCoefficient 19 31 3 2) v1683_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1683_upper : Scalar.QComplex := ((999997748399788220612516017991 : Int)/10^30,(-2122073362034230258383564140 : Int)/10^30)
theorem v1683_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 31 5) 1) 14) v1683_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1683 : Material (19 : Basis) (31 : Basis) where
  plus := ![v1683_pa,v1683_pb,v1683_pg]
  minus := ![(Primitive.Addresses.material1683 1).one,v1683_mb,v1683_mg]
  upper := v1683_upper
  lower := (Primitive.Addresses.material1683 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1683_pa_checked.trans (by decide +kernel)
    · exact v1683_pb_checked.trans (by decide +kernel)
    · exact v1683_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 31 Primitive.Addresses.material1683
    · exact v1683_mb_checked.trans (by decide +kernel)
    · exact v1683_mg_checked.trans (by decide +kernel)
  upper_error := v1683_upper_checked
  lower_error := reuse_lower_error 19 31 Primitive.Addresses.material1683

def v1684_pa : Scalar.QComplex := ((999999919623195529939081084649 : Int)/10^30,(-400940896491853448607020407 : Int)/10^30)
theorem v1684_pa_checked : Scalar.distance (sourceCoefficient 19 32 1 0) v1684_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1684_pb : Scalar.QComplex := ((-172996982984244254599014 : Int)/10^30,(-431477483571732954557276692 : Int)/10^30)
theorem v1684_pb_checked : Scalar.distance (sourceCoefficient 19 32 1 1) v1684_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1684_pg : Scalar.QComplex := ((-93086422118546604055183 : Int)/10^30,(37322156535264849621 : Int)/10^30)
theorem v1684_pg_checked : Scalar.distance (sourceCoefficient 19 32 1 2) v1684_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1684_mb : Scalar.QComplex := ((-545342553867494383331095 : Int)/10^30,(-431477173624341505115976878 : Int)/10^30)
theorem v1684_mb_checked : Scalar.distance (sourceCoefficient 19 32 3 1) v1684_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1684_mg : Scalar.QComplex := ((-93086355250877227262594 : Int)/10^30,(117651532470005077391 : Int)/10^30)
theorem v1684_mg_checked : Scalar.distance (sourceCoefficient 19 32 3 2) v1684_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1684_upper : Scalar.QComplex := ((999997738253169222502065621612 : Int)/10^30,(-2126849441323073375365577358 : Int)/10^30)
theorem v1684_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 32 5) 1) 14) v1684_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1684 : Material (19 : Basis) (32 : Basis) where
  plus := ![v1684_pa,v1684_pb,v1684_pg]
  minus := ![(Primitive.Addresses.material1684 1).one,v1684_mb,v1684_mg]
  upper := v1684_upper
  lower := (Primitive.Addresses.material1684 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1684_pa_checked.trans (by decide +kernel)
    · exact v1684_pb_checked.trans (by decide +kernel)
    · exact v1684_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 32 Primitive.Addresses.material1684
    · exact v1684_mb_checked.trans (by decide +kernel)
    · exact v1684_mg_checked.trans (by decide +kernel)
  upper_error := v1684_upper_checked
  lower_error := reuse_lower_error 19 32 Primitive.Addresses.material1684

def v1685_pa : Scalar.QComplex := ((999999916932333827597093011054 : Int)/10^30,(-407597013537352418428265815 : Int)/10^30)
theorem v1685_pa_checked : Scalar.distance (sourceCoefficient 19 33 1 0) v1685_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1685_pb : Scalar.QComplex := ((-175868947770656896059274 : Int)/10^30,(-431477482220357645226747069 : Int)/10^30)
theorem v1685_pb_checked : Scalar.distance (sourceCoefficient 19 33 1 1) v1685_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1685_pg : Scalar.QComplex := ((-93086421847533225722925 : Int)/10^30,(37941750697665379076 : Int)/10^30)
theorem v1685_pg_checked : Scalar.distance (sourceCoefficient 19 33 1 2) v1685_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1685_mb : Scalar.QComplex := ((-548214516418367251267366 : Int)/10^30,(-431477169794590436782464528 : Int)/10^30)
theorem v1685_mb_checked : Scalar.distance (sourceCoefficient 19 33 3 1) v1685_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1685_mg : Scalar.QComplex := ((-93086354445182093174519 : Int)/10^30,(118271126167830043821 : Int)/10^30)
theorem v1685_mg_checked : Scalar.distance (sourceCoefficient 19 33 3 2) v1685_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1685_upper : Scalar.QComplex := ((999997724074457345572712793120 : Int)/10^30,(-2133505543810884703172975173 : Int)/10^30)
theorem v1685_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 33 5) 1) 14) v1685_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1685 : Material (19 : Basis) (33 : Basis) where
  plus := ![v1685_pa,v1685_pb,v1685_pg]
  minus := ![(Primitive.Addresses.material1685 1).one,v1685_mb,v1685_mg]
  upper := v1685_upper
  lower := (Primitive.Addresses.material1685 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1685_pa_checked.trans (by decide +kernel)
    · exact v1685_pb_checked.trans (by decide +kernel)
    · exact v1685_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 33 Primitive.Addresses.material1685
    · exact v1685_mb_checked.trans (by decide +kernel)
    · exact v1685_mg_checked.trans (by decide +kernel)
  upper_error := v1685_upper_checked
  lower_error := reuse_lower_error 19 33 Primitive.Addresses.material1685

def v1686_pa : Scalar.QComplex := ((999999910212041713687289088397 : Int)/10^30,(-423763977363281751372888783 : Int)/10^30)
theorem v1686_pa_checked : Scalar.distance (sourceCoefficient 19 34 1 0) v1686_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1686_pb : Scalar.QComplex := ((-182844628989724790292983 : Int)/10^30,(-431477478831880453819805684 : Int)/10^30)
theorem v1686_pb_checked : Scalar.distance (sourceCoefficient 19 34 1 1) v1686_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1686_pg : Scalar.QComplex := ((-93086421169236274120605 : Int)/10^30,(39446675615025616341 : Int)/10^30)
theorem v1686_pg_checked : Scalar.distance (sourceCoefficient 19 34 1 2) v1686_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1686_mb : Scalar.QComplex := ((-555190192115967018424443 : Int)/10^30,(-431477160386415788024305965 : Int)/10^30)
theorem v1686_mb_checked : Scalar.distance (sourceCoefficient 19 34 3 1) v1686_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1686_mg : Scalar.QComplex := ((-93086352468202969753462 : Int)/10^30,(119776049939498236014 : Int)/10^30)
theorem v1686_mg_checked : Scalar.distance (sourceCoefficient 19 34 3 2) v1686_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1686_upper : Scalar.QComplex := ((999997689451462332695967178678 : Int)/10^30,(-2149672471959405993901547515 : Int)/10^30)
theorem v1686_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 34 5) 1) 14) v1686_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1686 : Material (19 : Basis) (34 : Basis) where
  plus := ![v1686_pa,v1686_pb,v1686_pg]
  minus := ![(Primitive.Addresses.material1686 1).one,v1686_mb,v1686_mg]
  upper := v1686_upper
  lower := (Primitive.Addresses.material1686 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1686_pa_checked.trans (by decide +kernel)
    · exact v1686_pb_checked.trans (by decide +kernel)
    · exact v1686_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 34 Primitive.Addresses.material1686
    · exact v1686_mb_checked.trans (by decide +kernel)
    · exact v1686_mg_checked.trans (by decide +kernel)
  upper_error := v1686_upper_checked
  lower_error := reuse_lower_error 19 34 Primitive.Addresses.material1686

def v1687_pa : Scalar.QComplex := ((999999887127599455974698057838 : Int)/10^30,(-475126076265944173565749927 : Int)/10^30)
theorem v1687_pa_checked : Scalar.distance (sourceCoefficient 19 35 1 0) v1687_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1687_pb : Scalar.QComplex := ((-205006219065234487148023 : Int)/10^30,(-431477467069059574008216855 : Int)/10^30)
theorem v1687_pb_checked : Scalar.distance (sourceCoefficient 19 35 1 1) v1687_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1687_pg : Scalar.QComplex := ((-93086418825963860218436 : Int)/10^30,(44227789922525345861 : Int)/10^30)
theorem v1687_pg_checked : Scalar.distance (sourceCoefficient 19 35 1 2) v1687_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1687_mb : Scalar.QComplex := ((-577351763788919253974472 : Int)/10^30,(-431477129499145173848658867 : Int)/10^30)
theorem v1687_mb_checked : Scalar.distance (sourceCoefficient 19 35 3 1) v1687_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1687_mg : Scalar.QComplex := ((-93086345999045114381297 : Int)/10^30,(124557160444632045007 : Int)/10^30)
theorem v1687_mg_checked : Scalar.distance (sourceCoefficient 19 35 3 2) v1687_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1687_upper : Scalar.QComplex := ((999997577720731283767262777432 : Int)/10^30,(-2201034454522602383970854595 : Int)/10^30)
theorem v1687_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 35 5) 1) 14) v1687_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1687 : Material (19 : Basis) (35 : Basis) where
  plus := ![v1687_pa,v1687_pb,v1687_pg]
  minus := ![(Primitive.Addresses.material1687 1).one,v1687_mb,v1687_mg]
  upper := v1687_upper
  lower := (Primitive.Addresses.material1687 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1687_pa_checked.trans (by decide +kernel)
    · exact v1687_pb_checked.trans (by decide +kernel)
    · exact v1687_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 35 Primitive.Addresses.material1687
    · exact v1687_mb_checked.trans (by decide +kernel)
    · exact v1687_mg_checked.trans (by decide +kernel)
  upper_error := v1687_upper_checked
  lower_error := reuse_lower_error 19 35 Primitive.Addresses.material1687

def v1688_pa : Scalar.QComplex := ((999999879326395632360596817012 : Int)/10^30,(-491270998709632782744523128 : Int)/10^30)
theorem v1688_pa_checked : Scalar.distance (sourceCoefficient 19 36 1 0) v1688_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1688_pb : Scalar.QComplex := ((-211972389776713446203750 : Int)/10^30,(-431477463058078980318980929 : Int)/10^30)
theorem v1688_pb_checked : Scalar.distance (sourceCoefficient 19 36 1 1) v1688_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1688_pg : Scalar.QComplex := ((-93086418030208743293381 : Int)/10^30,(45730663070486960166 : Int)/10^30)
theorem v1688_pg_checked : Scalar.distance (sourceCoefficient 19 36 1 2) v1688_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1688_mb : Scalar.QComplex := ((-584317928445278882923449 : Int)/10^30,(-431477119476674494306562128 : Int)/10^30)
theorem v1688_mb_checked : Scalar.distance (sourceCoefficient 19 36 3 1) v1688_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1688_mg : Scalar.QComplex := ((-93086343906378453955295 : Int)/10^30,(126060032346304475205 : Int)/10^30)
theorem v1688_mg_checked : Scalar.distance (sourceCoefficient 19 36 3 2) v1688_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1688_upper : Scalar.QComplex := ((999997542054867597246150832645 : Int)/10^30,(-2217179339456155449213186547 : Int)/10^30)
theorem v1688_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 36 5) 1) 14) v1688_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1688 : Material (19 : Basis) (36 : Basis) where
  plus := ![v1688_pa,v1688_pb,v1688_pg]
  minus := ![(Primitive.Addresses.material1688 1).one,v1688_mb,v1688_mg]
  upper := v1688_upper
  lower := (Primitive.Addresses.material1688 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1688_pa_checked.trans (by decide +kernel)
    · exact v1688_pb_checked.trans (by decide +kernel)
    · exact v1688_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 36 Primitive.Addresses.material1688
    · exact v1688_mb_checked.trans (by decide +kernel)
    · exact v1688_mg_checked.trans (by decide +kernel)
  upper_error := v1688_upper_checked
  lower_error := reuse_lower_error 19 36 Primitive.Addresses.material1688

def v1689_pa : Scalar.QComplex := ((999999875915781442007013487754 : Int)/10^30,(-498165054694819674559054311 : Int)/10^30)
theorem v1689_pa_checked : Scalar.distance (sourceCoefficient 19 37 1 0) v1689_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1689_pb : Scalar.QComplex := ((-214947019779459400608889 : Int)/10^30,(-431477461299658708427611659 : Int)/10^30)
theorem v1689_pb_checked : Scalar.distance (sourceCoefficient 19 37 1 1) v1689_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1689_pg : Scalar.QComplex := ((-93086417681788080350536 : Int)/10^30,(46372406109876563102 : Int)/10^30)
theorem v1689_pg_checked : Scalar.distance (sourceCoefficient 19 37 1 2) v1689_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1689_mb : Scalar.QComplex := ((-587292555822996641666100 : Int)/10^30,(-431477115151283157147701036 : Int)/10^30)
theorem v1689_mb_checked : Scalar.distance (sourceCoefficient 19 37 3 1) v1689_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1689_mg : Scalar.QComplex := ((-93086343004162580785722 : Int)/10^30,(126701774846072475634 : Int)/10^30)
theorem v1689_mg_checked : Scalar.distance (sourceCoefficient 19 37 3 2) v1689_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1689_upper : Scalar.QComplex := ((999997526745743280042622843340 : Int)/10^30,(-2224073379287045099747604590 : Int)/10^30)
theorem v1689_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 37 5) 1) 14) v1689_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1689 : Material (19 : Basis) (37 : Basis) where
  plus := ![v1689_pa,v1689_pb,v1689_pg]
  minus := ![(Primitive.Addresses.material1689 1).one,v1689_mb,v1689_mg]
  upper := v1689_upper
  lower := (Primitive.Addresses.material1689 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1689_pa_checked.trans (by decide +kernel)
    · exact v1689_pb_checked.trans (by decide +kernel)
    · exact v1689_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 37 Primitive.Addresses.material1689
    · exact v1689_mb_checked.trans (by decide +kernel)
    · exact v1689_mg_checked.trans (by decide +kernel)
  upper_error := v1689_upper_checked
  lower_error := reuse_lower_error 19 37 Primitive.Addresses.material1689

def v1690_pa : Scalar.QComplex := ((999999864036560888069709935392 : Int)/10^30,(-521466067676319477110130476 : Int)/10^30)
theorem v1690_pa_checked : Scalar.distance (sourceCoefficient 19 38 1 0) v1690_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1690_pb : Scalar.QComplex := ((-225000882422057547683548 : Int)/10^30,(-431477455154042005013049380 : Int)/10^30)
theorem v1690_pb_checked : Scalar.distance (sourceCoefficient 19 38 1 1) v1690_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1690_pg : Scalar.QComplex := ((-93086416465967069465102 : Int)/10^30,(48541414148445650555 : Int)/10^30)
theorem v1690_pg_checked : Scalar.distance (sourceCoefficient 19 38 1 2) v1690_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1690_mb : Scalar.QComplex := ((-597346409418691815934411 : Int)/10^30,(-431477100329638090629261394 : Int)/10^30)
theorem v1690_mb_checked : Scalar.distance (sourceCoefficient 19 38 3 1) v1690_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1690_mg : Scalar.QComplex := ((-93086339916585773816584 : Int)/10^30,(128870781027821967915 : Int)/10^30)
theorem v1690_mg_checked : Scalar.distance (sourceCoefficient 19 38 3 2) v1690_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1690_upper : Scalar.QComplex := ((999997474651105864125424728005 : Int)/10^30,(-2247374337061966193986911609 : Int)/10^30)
theorem v1690_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 38 5) 1) 14) v1690_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1690 : Material (19 : Basis) (38 : Basis) where
  plus := ![v1690_pa,v1690_pb,v1690_pg]
  minus := ![(Primitive.Addresses.material1690 1).one,v1690_mb,v1690_mg]
  upper := v1690_upper
  lower := (Primitive.Addresses.material1690 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1690_pa_checked.trans (by decide +kernel)
    · exact v1690_pb_checked.trans (by decide +kernel)
    · exact v1690_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 38 Primitive.Addresses.material1690
    · exact v1690_mb_checked.trans (by decide +kernel)
    · exact v1690_mg_checked.trans (by decide +kernel)
  upper_error := v1690_upper_checked
  lower_error := reuse_lower_error 19 38 Primitive.Addresses.material1690

def v1691_pa : Scalar.QComplex := ((999999856896338800600863941402 : Int)/10^30,(-534983459482758610123426284 : Int)/10^30)
theorem v1691_pa_checked : Scalar.distance (sourceCoefficient 19 39 1 0) v1691_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1691_pb : Scalar.QComplex := ((-230833332696310870205715 : Int)/10^30,(-431477451445683631398301647 : Int)/10^30)
theorem v1691_pb_checked : Scalar.distance (sourceCoefficient 19 39 1 1) v1691_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1691_pg : Scalar.QComplex := ((-93086415733619840337562 : Int)/10^30,(49799699846541608127 : Int)/10^30)
theorem v1691_pg_checked : Scalar.distance (sourceCoefficient 19 39 1 2) v1691_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1691_mb : Scalar.QComplex := ((-603178854321111087038002 : Int)/10^30,(-431477091588139194934270185 : Int)/10^30)
theorem v1691_mb_checked : Scalar.distance (sourceCoefficient 19 39 3 1) v1691_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1691_mg : Scalar.QComplex := ((-93086338098394931002689 : Int)/10^30,(130129065625417978546 : Int)/10^30)
theorem v1691_mg_checked : Scalar.distance (sourceCoefficient 19 39 3 2) v1691_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1691_upper : Scalar.QComplex := ((999997444181102441470127422975 : Int)/10^30,(-2260891696412462528608648081 : Int)/10^30)
theorem v1691_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 39 5) 1) 14) v1691_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1691 : Material (19 : Basis) (39 : Basis) where
  plus := ![v1691_pa,v1691_pb,v1691_pg]
  minus := ![(Primitive.Addresses.material1691 1).one,v1691_mb,v1691_mg]
  upper := v1691_upper
  lower := (Primitive.Addresses.material1691 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1691_pa_checked.trans (by decide +kernel)
    · exact v1691_pb_checked.trans (by decide +kernel)
    · exact v1691_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 39 Primitive.Addresses.material1691
    · exact v1691_mb_checked.trans (by decide +kernel)
    · exact v1691_mg_checked.trans (by decide +kernel)
  upper_error := v1691_upper_checked
  lower_error := reuse_lower_error 19 39 Primitive.Addresses.material1691

def v1692_pa : Scalar.QComplex := ((999999844474771669351142874267 : Int)/10^30,(-557718954737241351140703183 : Int)/10^30)
theorem v1692_pa_checked : Scalar.distance (sourceCoefficient 19 40 1 0) v1692_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1692_pb : Scalar.QComplex := ((-240643187028199200219417 : Int)/10^30,(-431477444971342280983853416 : Int)/10^30)
theorem v1692_pb_checked : Scalar.distance (sourceCoefficient 19 40 1 1) v1692_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1692_pg : Scalar.QComplex := ((-93086414457096950501523 : Int)/10^30,(51916065845507737729 : Int)/10^30)
theorem v1692_pg_checked : Scalar.distance (sourceCoefficient 19 40 1 2) v1692_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1692_mb : Scalar.QComplex := ((-612988699413277324900932 : Int)/10^30,(-431477076648337786231369699 : Int)/10^30)
theorem v1692_mb_checked : Scalar.distance (sourceCoefficient 19 40 3 1) v1692_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1692_mg : Scalar.QComplex := ((-93086334995543976952930 : Int)/10^30,(132245429734782562557 : Int)/10^30)
theorem v1692_mg_checked : Scalar.distance (sourceCoefficient 19 40 3 2) v1692_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1692_upper : Scalar.QComplex := ((999997392520151549466043328321 : Int)/10^30,(-2283627136366597794183295689 : Int)/10^30)
theorem v1692_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 40 5) 1) 14) v1692_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1692 : Material (19 : Basis) (40 : Basis) where
  plus := ![v1692_pa,v1692_pb,v1692_pg]
  minus := ![(Primitive.Addresses.material1692 1).one,v1692_mb,v1692_mg]
  upper := v1692_upper
  lower := (Primitive.Addresses.material1692 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1692_pa_checked.trans (by decide +kernel)
    · exact v1692_pb_checked.trans (by decide +kernel)
    · exact v1692_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 40 Primitive.Addresses.material1692
    · exact v1692_mb_checked.trans (by decide +kernel)
    · exact v1692_mg_checked.trans (by decide +kernel)
  upper_error := v1692_upper_checked
  lower_error := reuse_lower_error 19 40 Primitive.Addresses.material1692

def v1693_pa : Scalar.QComplex := ((999999836291880446044786933835 : Int)/10^30,(-572202946783361137768925444 : Int)/10^30)
theorem v1693_pa_checked : Scalar.distance (sourceCoefficient 19 41 1 0) v1693_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1693_pb : Scalar.QComplex := ((-246892703452671416511149 : Int)/10^30,(-431477440691695676484921057 : Int)/10^30)
theorem v1693_pb_checked : Scalar.distance (sourceCoefficient 19 41 1 1) v1693_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1693_pg : Scalar.QComplex := ((-93086413614596037395544 : Int)/10^30,(53264328895569762875 : Int)/10^30)
theorem v1693_pg_checked : Scalar.distance (sourceCoefficient 19 41 1 2) v1693_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1693_mb : Scalar.QComplex := ((-619238209817626687796634 : Int)/10^30,(-431477066975641568692118471 : Int)/10^30)
theorem v1693_mb_checked : Scalar.distance (sourceCoefficient 19 41 3 1) v1693_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1693_mg : Scalar.QComplex := ((-93086332989553088858629 : Int)/10^30,(133593691555784292321 : Int)/10^30)
theorem v1693_mg_checked : Scalar.distance (sourceCoefficient 19 41 3 2) v1693_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1693_upper : Scalar.QComplex := ((999997359339216219506377943346 : Int)/10^30,(-2298111092717584932005430822 : Int)/10^30)
theorem v1693_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 41 5) 1) 14) v1693_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1693 : Material (19 : Basis) (41 : Basis) where
  plus := ![v1693_pa,v1693_pb,v1693_pg]
  minus := ![(Primitive.Addresses.material1693 1).one,v1693_mb,v1693_mg]
  upper := v1693_upper
  lower := (Primitive.Addresses.material1693 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1693_pa_checked.trans (by decide +kernel)
    · exact v1693_pb_checked.trans (by decide +kernel)
    · exact v1693_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 41 Primitive.Addresses.material1693
    · exact v1693_mb_checked.trans (by decide +kernel)
    · exact v1693_mg_checked.trans (by decide +kernel)
  upper_error := v1693_upper_checked
  lower_error := reuse_lower_error 19 41 Primitive.Addresses.material1693

def v1694_pa : Scalar.QComplex := ((999999829538207691755927527203 : Int)/10^30,(-583886594776130742440266567 : Int)/10^30)
theorem v1694_pa_checked : Scalar.distance (sourceCoefficient 19 42 1 0) v1694_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1694_pb : Scalar.QComplex := ((-251933934446251063714905 : Int)/10^30,(-431477437151533832093146595 : Int)/10^30)
theorem v1694_pb_checked : Scalar.distance (sourceCoefficient 19 42 1 1) v1694_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1694_pg : Scalar.QComplex := ((-93086412918383313103501 : Int)/10^30,(54351917923765004119 : Int)/10^30)
theorem v1694_pg_checked : Scalar.distance (sourceCoefficient 19 42 1 2) v1694_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1694_mb : Scalar.QComplex := ((-624279435879125411713074 : Int)/10^30,(-431477059085125743620666566 : Int)/10^30)
theorem v1694_mb_checked : Scalar.distance (sourceCoefficient 19 42 3 1) v1694_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1694_mg : Scalar.QComplex := ((-93086331354800275657397 : Int)/10^30,(134681279578220208288 : Int)/10^30)
theorem v1694_mg_checked : Scalar.distance (sourceCoefficient 19 42 3 2) v1694_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1694_upper : Scalar.QComplex := ((999997332420637020765573830124 : Int)/10^30,(-2309794711652706823653210382 : Int)/10^30)
theorem v1694_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 42 5) 1) 14) v1694_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1694 : Material (19 : Basis) (42 : Basis) where
  plus := ![v1694_pa,v1694_pb,v1694_pg]
  minus := ![(Primitive.Addresses.material1694 1).one,v1694_mb,v1694_mg]
  upper := v1694_upper
  lower := (Primitive.Addresses.material1694 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1694_pa_checked.trans (by decide +kernel)
    · exact v1694_pb_checked.trans (by decide +kernel)
    · exact v1694_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 42 Primitive.Addresses.material1694
    · exact v1694_mb_checked.trans (by decide +kernel)
    · exact v1694_mg_checked.trans (by decide +kernel)
  upper_error := v1694_upper_checked
  lower_error := reuse_lower_error 19 42 Primitive.Addresses.material1694

def v1695_pa : Scalar.QComplex := ((999999820381153524167127439257 : Int)/10^30,(-599364380563890146003249161 : Int)/10^30)
theorem v1695_pa_checked : Scalar.distance (sourceCoefficient 19 43 1 0) v1695_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1695_pb : Scalar.QComplex := ((-258612250413884146547033 : Int)/10^30,(-431477432340814398023054220 : Int)/10^30)
theorem v1695_pb_checked : Scalar.distance (sourceCoefficient 19 43 1 1) v1695_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1695_pg : Scalar.QComplex := ((-93086411973255225025325 : Int)/10^30,(55792689672683765759 : Int)/10^30)
theorem v1695_pg_checked : Scalar.distance (sourceCoefficient 19 43 1 2) v1695_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1695_mb : Scalar.QComplex := ((-630957745208682040835573 : Int)/10^30,(-431477048511322200919626613 : Int)/10^30)
theorem v1695_mb_checked : Scalar.distance (sourceCoefficient 19 43 3 1) v1695_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1695_mg : Scalar.QComplex := ((-93086329166351410127454 : Int)/10^30,(136122049975070828261 : Int)/10^30)
theorem v1695_mg_checked : Scalar.distance (sourceCoefficient 19 43 3 2) v1695_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1695_upper : Scalar.QComplex := ((999997296550342355618737219619 : Int)/10^30,(-2325272458583877672991728072 : Int)/10^30)
theorem v1695_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 43 5) 1) 14) v1695_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1695 : Material (19 : Basis) (43 : Basis) where
  plus := ![v1695_pa,v1695_pb,v1695_pg]
  minus := ![(Primitive.Addresses.material1695 1).one,v1695_mb,v1695_mg]
  upper := v1695_upper
  lower := (Primitive.Addresses.material1695 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1695_pa_checked.trans (by decide +kernel)
    · exact v1695_pb_checked.trans (by decide +kernel)
    · exact v1695_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 43 Primitive.Addresses.material1695
    · exact v1695_mb_checked.trans (by decide +kernel)
    · exact v1695_mg_checked.trans (by decide +kernel)
  upper_error := v1695_upper_checked
  lower_error := reuse_lower_error 19 43 Primitive.Addresses.material1695

def v1696_pa : Scalar.QComplex := ((999999816854262842865091203060 : Int)/10^30,(-605220158927235981045897625 : Int)/10^30)
theorem v1696_pa_checked : Scalar.distance (sourceCoefficient 19 44 1 0) v1696_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1696_pb : Scalar.QComplex := ((-261138886878011563758377 : Int)/10^30,(-431477430484819092123714507 : Int)/10^30)
theorem v1696_pb_checked : Scalar.distance (sourceCoefficient 19 44 1 1) v1696_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1696_pg : Scalar.QComplex := ((-93086411608897321379240 : Int)/10^30,(56337783145927765301 : Int)/10^30)
theorem v1696_pg_checked : Scalar.distance (sourceCoefficient 19 44 1 2) v1696_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1696_mb : Scalar.QComplex := ((-633484379130386871395795 : Int)/10^30,(-431477044474954113032258850 : Int)/10^30)
theorem v1696_mb_checked : Scalar.distance (sourceCoefficient 19 44 3 1) v1696_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1696_mg : Scalar.QComplex := ((-93086328331602524837590 : Int)/10^30,(136667142930927154936 : Int)/10^30)
theorem v1696_mg_checked : Scalar.distance (sourceCoefficient 19 44 3 2) v1696_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1696_upper : Scalar.QComplex := ((999997282916914704134527404082 : Int)/10^30,(-2331128222138636144973334742 : Int)/10^30)
theorem v1696_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 44 5) 1) 14) v1696_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1696 : Material (19 : Basis) (44 : Basis) where
  plus := ![v1696_pa,v1696_pb,v1696_pg]
  minus := ![(Primitive.Addresses.material1696 1).one,v1696_mb,v1696_mg]
  upper := v1696_upper
  lower := (Primitive.Addresses.material1696 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1696_pa_checked.trans (by decide +kernel)
    · exact v1696_pb_checked.trans (by decide +kernel)
    · exact v1696_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 44 Primitive.Addresses.material1696
    · exact v1696_mb_checked.trans (by decide +kernel)
    · exact v1696_mg_checked.trans (by decide +kernel)
  upper_error := v1696_upper_checked
  lower_error := reuse_lower_error 19 44 Primitive.Addresses.material1696

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
