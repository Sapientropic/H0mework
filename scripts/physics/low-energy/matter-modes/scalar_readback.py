#!/usr/bin/env python3
"""Read the original70 scalar vertices on the actual free external carrier."""
import argparse
import json
from pathlib import Path
import sympy as s
from compute import clean,decode,zero


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--vertices',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    source=json.loads(args.source.read_text());vertices=json.loads(args.vertices.read_text())
    assert source['source_sha256']==vertices['source_sha256']
    F=decode(source['source_isometry'])
    left=clean(decode(source['canonical_dual_frame']).T/s.sqrt(2))
    checked=[]
    for vertex in vertices['primitive_vertices']:
        if vertex['group']!='scalar':continue
        action=decode(vertex['operator'])
        zero(left*action)
        bilinear=clean(left*action*F)
        zero(bilinear+bilinear.H)
        checked.append(vertex['coordinate'])
    assert len(checked)==70
    result={'scope':'ALL_ORIGINAL_SCALAR_SOURCE_VERTICES_ON_FREE_CANONICAL_EXTERNAL_LEGS',
        'source_sha256':source['source_sha256'],'actual_scalar_coordinates':checked,
        'source_dual_identity':'F^dagger S V_scalar=0 on every primal column',
        'canonical_real_free_free_source':'F^dagger (S V_scalar+V_scalar^dagger S) F=0',
        'all_70_original_complex_and_real_bilinear_rows_zero':True,
        'mixed_free_interacting_Hermitian_vertices_not_discarded':True}
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS all70 original scalar vertices annihilated by source free canonical dual; all free-free real scalar sources vanish')


if __name__=='__main__':main()
