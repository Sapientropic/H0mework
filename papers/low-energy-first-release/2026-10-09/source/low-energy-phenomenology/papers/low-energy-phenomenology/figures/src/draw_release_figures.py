#!/usr/bin/env python3
"""Draw action/clock, same-transfer Newton and conditional Born-dressing plates."""
import argparse
import json
from pathlib import Path

from svg_plate import SVGPlate, SVG_FONT_ZH, SVG_FONT_EN, INK, SLATE, HAIR, DEEP, VERMILION, WASH

BASE = Path(__file__).resolve().parents[1]
SOURCE = '71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9'
PREFIX = 'Verification/physics/low-energy-phenomenology/alpha-source/em-identification/'


def draw(language):
    records = []
    text = lambda zh, en: zh if language == 'zh' else en
    def plate(title, height):
        return SVGPlate(title, height, base=BASE, source_commit=SOURCE,
                        font=SVG_FONT_ZH if language == 'zh' else SVG_FONT_EN,
                        suffix='' if language == 'zh' else '-en', manifest=records,
                        creator='draw_release_figures.py')

    g = plate(text('同一原作用的物理时钟与通量', 'The physical clock and flux of one original action'), 496)
    g.box(55, 22, 890, 86, text('原作用的 Fourier Hessian，完整 289 行', 'The original Fourier Hessian, all 289 rows'),
          [r'$K(\omega)=\mathcal{H}_{\mathrm{original}}(\omega),\qquad G(\omega),\qquad \mathrm{E}=-\mathrm{color}_2-Y/2$'])
    g.line(315, 108, 270, 142, arrow=True)
    g.line(685, 108, 730, 142, arrow=True)
    g.box(65, 148, 410, 145, text('原物理频率', 'Original physical frequency'),
          [r'$R_\omega=\mathrm{Res}_{\omega=\omega_*}G(\omega)$',
           r"$K'_\omega=\partial_\omega K(\omega_*)$", r"$P=R_\omega K'_\omega$"])
    g.box(525, 148, 410, 145, text('时钟重表达，正尺度', 'Clock re-expression, positive scale'),
          [r"$t'=ct,\quad \omega'=\omega/c,\quad c>0$",
           r"$R_c=R_\omega/c,\quad K'_c=cK'_\omega$", r"$R_cK'_c=P$"])
    g.line(475, 218, 523, 218, arrow=True)
    g.line(270, 293, 270, 318)
    g.line(730, 293, 730, 318)
    g.line(270, 318, 730, 318)
    g.line(500, 318, 500, 347, arrow=True)
    g.box(85, 354, 830, 126, text('通量恒等式随同一时钟返回', 'The flux identity returns with the same clock'),
          [r"$\mathcal{E}^{\mathsf{T}}R_cK'_cR_c\mathcal{E}=\mathcal{E}^{\mathsf{T}}R_c\mathcal{E}$",
           text('两边同缩为原值的 1/c；归一投影 P 保持', 'Both sides scale by 1/c; the normalized projector P is retained')],
          fill=WASH, edge=VERMILION, title_fill=VERMILION, lw=2)
    g.save('main-04-action-clock')

    g = plate(text('两个实际端，同一次 Fourier 转移', 'Two actual endpoints, one Fourier transfer'), 550)
    g.box(45, 18, 400, 120, text('detector：完整 connected 电流', 'Detector: full connected current'),
          [r'$J_D(-a\mathbf{k})$', text('独立准备与年龄窗', 'Independent preparation and age window')])
    g.box(555, 18, 400, 120, text('source：完整 connected 电流', 'Source: full connected current'),
          [r'$J_S(+a\mathbf{k})$', text('独立准备与年龄窗', 'Independent preparation and age window')])
    g.line(245, 138, 355, 172, arrow=True)
    g.line(755, 138, 645, 172, arrow=True)
    g.box(105, 178, 790, 118, text('同一 whole289 Green；原源生成 IR 半径', 'The same whole289 Green; source-generated IR radius'),
          [r'$0<a|\mathbf{k}|<r_{D,S},\qquad \mathbf{k}=2\pi\xi$',
           r'$\|m_a(\mathbf{k})\|\leq B_{D,S}/|\mathbf{k}|^2$'])
    g.line(500, 296, 500, 327, arrow=True)
    g.box(105, 332, 790, 86, text('Schwartz 输入上的真实 Fourier 积分', 'An actual Fourier integral on Schwartz input'),
          [r'$\mathcal{O}_a(x)=\int e^{2\pi i\xi\cdot x}\,\phi(\xi)m_a(2\pi\xi)\,d^3\xi$'])
    g.line(500, 418, 500, 443, arrow=True)
    g.box(85, 448, 830, 86, text('同一次转移返回 Newton 空间观测', 'The same transfer returns to Newton space'),
          [r'$\mathcal{O}_a(x)\longrightarrow C_0\int\frac{f(x-y)}{4\pi|y|}\,d^3y,\qquad f=\mathcal{F}^{-1}\phi$'],
          fill=WASH, edge=VERMILION, title_fill=VERMILION, lw=2)
    g.save('main-05-newton-return')

    g = plate(text('Born 重叠自产 Coulomb 修饰', 'Born overlaps generate Coulomb dressing'), 500)
    g.text(500, 30, text('每一对至少一端为独立 sharp；保完整 N3 复合响应',
                        'At least one independent sharp leg in each pair; full N3 responses'), 19, 'middle', '600')
    for x, label, symbol in [(35, 'detector 1', 'D1'), (280, 'detector 2', 'D2'),
                              (525, 'source 1', 'S1'), (770, 'source 2', 'S2')]:
        g.box(x, 56, 195, 120, label,
              [r'$z_{'+symbol+r'}=\|b_{'+symbol+r'}\|/\|r_{'+symbol+r'}\|$', r'$0<z_{'+symbol+r'}\leq1$'])
        g.line(x+97.5, 176, x+97.5, 208)
    g.line(132.5, 208, 867.5, 208)
    g.line(500, 208, 500, 236, arrow=True)
    g.box(75, 242, 850, 90, text('单位 Born 读数固定重叠；四条腿合账', 'Unit Born readouts fix overlaps; all four legs combine'),
          [r'$p_j=z_j^2,\qquad z_{\mathrm{sharp}}=1,\qquad Z=z_{D1}z_{D2}z_{S1}z_{S2}$'])
    g.line(500, 332, 500, 365, arrow=True)
    g.box(65, 372, 870, 112, text('实际系数与差范数精确返回', 'The actual coefficient and norm difference return exactly'),
          [r'$C_{\mathrm{full}}=ZC_{\mathrm{base}}$',
           r'$\|C_{\mathrm{full}}-C_{\mathrm{base}}\|=(1-Z)\|C_{\mathrm{base}}\|$'],
          fill=WASH, edge=VERMILION, title_fill=VERMILION, lw=2)
    g.save('main-06-born-dressing')
    return records


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--language', choices=['zh', 'en', 'both'], default='both')
    args = parser.parse_args()
    records = []
    for language in ['zh', 'en'] if args.language == 'both' else [args.language]:
        records.extend(draw(language))
    manifest = {'source_commit': SOURCE, 'kind': 'Exact structural diagrams, no fitted data',
                'source_paths': [PREFIX + n for n in ['ActualEMAction.lean', 'ActualEMClock.lean',
                                 'ActualDressedMovingCoulomb.lean', 'ActualCompositeCoulombDressing.lean']],
                'figures': records}
    (BASE / 'release-figure-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'generated': len(records), 'languages': args.language}))
