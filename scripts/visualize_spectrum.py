#!/usr/bin/env python3
"""
visualize_spectrum.py

Reads the downward slice stream emitted by `cmd/Main.lean` (`level,x,local_degree`,
with or without a header row), constructs the exact Hermitian coherence matrix H
matching `TensorSieve/Operator.lean` on the largest horizontal slice, diagonalizes
H directly to obtain its real eigenvalues, and plots:
  1. Level-by-level diagonal Krein trace signature (-1)^Omega(x) * Omega(x)
  2. Cumulative eigenvalue density (exact staircase of H)
  3. Normalized nearest-neighbor eigenvalue spacing histogram with Poisson, GOE,
     and GUE Wigner surmises plus measured adjacent spacing ratio <r>
  4. Spectral Form Factor K(t) = (1/N) |sum_j exp(i E_j t)|^2 from unfolded eigenvalues

Runs with zero external dependencies (uses NumPy/Matplotlib when installed and falls
back to the pure-Python Hermitian Jacobi solver + vector SVG output otherwise).
"""

import argparse
import cmath
import csv
import math
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from adelic_operator_probe import (  # noqa: E402
    HAS_NUMPY,
    build_slice_operators,
    count_factors,
    hermitian_eigenvalues,
    parity_sign,
)

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False


def adjacent_spacing_ratio(eigs) -> float:
    sorted_e = sorted(float(x) for x in eigs)
    diffs = [sorted_e[i + 1] - sorted_e[i] for i in range(len(sorted_e) - 1)]
    diffs = [d for d in diffs if d > 1e-12]
    if len(diffs) < 2:
        return float('nan')
    ratios = [min(diffs[i], diffs[i + 1]) / max(diffs[i], diffs[i + 1]) for i in range(len(diffs) - 1)]
    return sum(ratios) / len(ratios)


def unfold_bulk_spacings(eigs):
    """
    Compute unfolded nearest-neighbor spacings over the spectral bulk.
    Drops up to 10% extreme edge eigenvalues when N >= 16 so sparse edge
    outliers do not distort the bulk mean spacing or histogram scale.
    """
    sorted_e = sorted(float(x) for x in eigs)
    n = len(sorted_e)
    if n < 3:
        return [float(i + 1) for i in range(n)], []
    trim = max(1, n // 10) if n >= 16 else 0
    bulk = sorted_e[trim : n - trim] if (n - 2 * trim) >= 6 else sorted_e
    mean_s = (bulk[-1] - bulk[0]) / (len(bulk) - 1) if len(bulk) > 1 else 1.0
    if mean_s <= 1e-12:
        mean_s = 1.0
    unfolded = [(e - bulk[0]) / mean_s for e in bulk]
    spacings = [unfolded[i + 1] - unfolded[i] for i in range(len(unfolded) - 1)]
    spacings = [s for s in spacings if s > 1e-12]
    return unfolded, spacings


def load_slices(csv_path: str):
    """Parse (level, x, local_degree) rows, tolerating headers or non-CSV #eval lines."""
    slices = defaultdict(list)
    with open(csv_path, 'r', newline='') as f:
        reader = csv.reader(f)
        for row in reader:
            if len(row) < 2:
                continue
            try:
                lvl = int(row[0].strip())
                x = int(row[1].strip())
            except ValueError:
                continue
            if x not in slices[lvl]:
                slices[lvl].append(x)
    return dict(slices)


def compute_sff(unfolded, num_points: int = 240):
    n_eigs = len(unfolded)
    t_vals = [10 ** (-2.0 + 3.5 * i / (num_points - 1)) for i in range(num_points)]
    k_vals = []
    for t in t_vals:
        s = sum(cmath.exp(1j * e * t) for e in unfolded)
        k_vals.append((abs(s) ** 2) / n_eigs)
    return t_vals, k_vals


def save_svg_plot(out_path, sorted_levels, level_traces, best_lvl, nodes, eigs, s_norm, r_val, t_vals, k_vals):
    """Pure-Python 4-panel vector SVG renderer (zero third-party dependencies)."""
    W, H_svg = 1280, 900
    panels = [
        (70, 50, 540, 350),
        (690, 50, 540, 350),
        (70, 480, 540, 350),
        (690, 480, 540, 350),
    ]
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H_svg}" viewBox="0 0 {W} {H_svg}">',
        '<style>text{font-family:system-ui,-apple-system,sans-serif;fill:#1f2937;} '
        '.title{font-size:15px;font-weight:600;} .axis{font-size:11px;fill:#4b5563;} '
        '.grid{stroke:#e5e7eb;stroke-width:1;} .frame{fill:#ffffff;stroke:#9ca3af;stroke-width:1.2;}</style>',
        f'<rect width="{W}" height="{H_svg}" fill="#f9fafb"/>',
    ]

    # Panel 1: Level-by-level diagonal trace bar chart
    x0, y0, pw, ph = panels[0]
    parts.append(f'<rect x="{x0}" y="{y0}" width="{pw}" height="{ph}" class="frame"/>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 - 14}" text-anchor="middle" class="title">'
                 'Diagonal Trace Signature by Factor-Weight Level</text>')
    max_abs = max((abs(v) for v in level_traces), default=1.0) or 1.0
    zero_y = y0 + ph / 2.0
    parts.append(f'<line x1="{x0}" y1="{zero_y:.1f}" x2="{x0 + pw}" y2="{zero_y:.1f}" stroke="#374151" stroke-width="1"/>')
    n_lvl = max(1, len(sorted_levels))
    bw = (pw - 20) / n_lvl
    for idx, (lv, tr) in enumerate(zip(sorted_levels, level_traces)):
        bh = (abs(tr) / max_abs) * (ph * 0.42)
        bx = x0 + 10 + idx * bw + bw * 0.12
        by = zero_y - bh if tr >= 0 else zero_y
        col = '#2ca02c' if tr >= 0 else '#f97316'
        parts.append(f'<rect x="{bx:.1f}" y="{by:.1f}" width="{bw * 0.76:.1f}" height="{max(1.0, bh):.1f}" '
                     f'fill="{col}" fill-opacity="0.82" stroke="#1f2937" stroke-width="0.6"/>')
        if idx % max(1, n_lvl // 8) == 0 or idx == n_lvl - 1:
            parts.append(f'<text x="{bx + bw * 0.38:.1f}" y="{y0 + ph + 16}" text-anchor="middle" class="axis">Ω={lv}</text>')
    parts.append(f'<text x="{x0 - 8}" y="{y0 + 14}" text-anchor="end" class="axis">+{int(max_abs)}</text>')
    parts.append(f'<text x="{x0 - 8}" y="{y0 + ph - 4}" text-anchor="end" class="axis">-{int(max_abs)}</text>')

    # Panel 2: Exact Eigenvalue Staircase
    x0, y0, pw, ph = panels[1]
    parts.append(f'<rect x="{x0}" y="{y0}" width="{pw}" height="{ph}" class="frame"/>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 - 14}" text-anchor="middle" class="title">'
                 f'Exact Eigenvalue Staircase (Level Ω={best_lvl}, d={len(nodes)})</text>')
    emin, emax = min(eigs), max(eigs)
    erng = (emax - emin) if emax > emin else 1.0
    n_e = len(eigs)
    pts = []
    for idx, ev in enumerate(eigs):
        px = x0 + 12 + ((ev - emin) / erng) * (pw - 24)
        py_prev = y0 + ph - 12 - (idx / n_e) * (ph - 24)
        py_next = y0 + ph - 12 - ((idx + 1) / n_e) * (ph - 24)
        pts.append(f'{px:.1f},{py_prev:.1f}')
        pts.append(f'{px:.1f},{py_next:.1f}')
    parts.append(f'<polyline fill="none" stroke="#0d9488" stroke-width="2" points="{" ".join(pts)}"/>')
    parts.append(f'<text x="{x0 + 12}" y="{y0 + ph + 16}" class="axis">λ={emin:.1f}</text>')
    parts.append(f'<text x="{x0 + pw - 12}" y="{y0 + ph + 16}" text-anchor="end" class="axis">λ={emax:.1f}</text>')
    parts.append(f'<text x="{x0 - 8}" y="{y0 + 16}" text-anchor="end" class="axis">{n_e}</text>')

    # Panel 3: Normalized Spacing Histogram + Poisson/GOE/GUE Surmises
    x0, y0, pw, ph = panels[2]
    parts.append(f'<rect x="{x0}" y="{y0}" width="{pw}" height="{ph}" class="frame"/>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 - 14}" text-anchor="middle" class="title">'
                 f'Bulk Eigenvalue Spacing (&lt;r&gt; = {r_val:.3f})</text>')
    s_max = 3.2
    n_bins = 12
    bin_w = s_max / n_bins
    counts = [0] * n_bins
    in_range = [s for s in s_norm if s <= s_max]
    for s in in_range:
        bi = min(n_bins - 1, int(s / bin_w))
        counts[bi] += 1
    densities = [c / (max(1, len(s_norm)) * bin_w) for c in counts]
    y_max = max(1.15, max(densities, default=1.0) * 1.12)
    for bi, dens in enumerate(densities):
        bx = x0 + 12 + (bi * bin_w / s_max) * (pw - 24)
        bw_px = (bin_w / s_max) * (pw - 24)
        bh = (dens / y_max) * (ph - 24)
        by = y0 + ph - 12 - bh
        parts.append(f'<rect x="{bx:.1f}" y="{by:.1f}" width="{bw_px:.1f}" height="{bh:.1f}" '
                     'fill="#4682b4" fill-opacity="0.6" stroke="#1f2937" stroke-width="0.7"/>')

    def curve_pts(fn):
        res = []
        for i in range(120):
            sv = s_max * i / 119.0
            pv = fn(sv)
            px = x0 + 12 + (sv / s_max) * (pw - 24)
            py = y0 + ph - 12 - (min(pv, y_max) / y_max) * (ph - 24)
            res.append(f'{px:.1f},{py:.1f}')
        return " ".join(res)

    parts.append(f'<polyline fill="none" stroke="#111827" stroke-width="1.4" stroke-dasharray="5,4" '
                 f'points="{curve_pts(lambda s: math.exp(-s))}"/>')
    parts.append(f'<polyline fill="none" stroke="#ea580c" stroke-width="1.6" stroke-dasharray="8,3,2,3" '
                 f'points="{curve_pts(lambda s: (math.pi / 2.0) * s * math.exp(-(math.pi / 4.0) * s * s))}"/>')
    parts.append(f'<polyline fill="none" stroke="#dc2626" stroke-width="2.0" '
                 f'points="{curve_pts(lambda s: (32.0 / (math.pi ** 2)) * s * s * math.exp(-(4.0 / math.pi) * s * s))}"/>')
    parts.append(f'<text x="{x0 + pw - 16}" y="{y0 + 22}" text-anchor="end" class="axis" style="fill:#dc2626;font-weight:600">GUE (0.600) —</text>')
    parts.append(f'<text x="{x0 + pw - 16}" y="{y0 + 38}" text-anchor="end" class="axis" style="fill:#ea580c;font-weight:600">GOE (0.531) -.-</text>')
    parts.append(f'<text x="{x0 + pw - 16}" y="{y0 + 54}" text-anchor="end" class="axis" style="fill:#111827">Poisson (0.386) --</text>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 + ph + 16}" text-anchor="middle" class="axis">Normalized Bulk Spacing s (0 .. {s_max:.1f})</text>')

    # Panel 4: Spectral Form Factor K(t) on log-log axes
    x0, y0, pw, ph = panels[3]
    parts.append(f'<rect x="{x0}" y="{y0}" width="{pw}" height="{ph}" class="frame"/>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 - 14}" text-anchor="middle" class="title">'
                 'Spectral Form Factor K(t) (Log-Log, Unfolded Bulk)</text>')
    log_t = [math.log10(t) for t in t_vals]
    log_k = [math.log10(max(k, 1e-4)) for k in k_vals]
    lt_min, lt_max = min(log_t), max(log_t)
    lk_min, lk_max = min(-2.5, min(log_k)), max(1.5, max(log_k))
    sff_pts = []
    for lt, lk in zip(log_t, log_k):
        px = x0 + 12 + ((lt - lt_min) / (lt_max - lt_min)) * (pw - 24)
        py = y0 + ph - 12 - ((lk - lk_min) / (lk_max - lk_min)) * (ph - 24)
        sff_pts.append(f'{px:.1f},{py:.1f}')
    plat_y = y0 + ph - 12 - ((0.0 - lk_min) / (lk_max - lk_min)) * (ph - 24)
    parts.append(f'<line x1="{x0 + 12}" y1="{plat_y:.1f}" x2="{x0 + pw - 12}" y2="{plat_y:.1f}" '
                 'stroke="#7e22ce" stroke-width="1.2" stroke-dasharray="5,4"/>')
    parts.append(f'<polyline fill="none" stroke="#111827" stroke-width="1.4" points="{" ".join(sff_pts)}"/>')
    parts.append(f'<text x="{x0 + 18}" y="{plat_y - 7:.1f}" text-anchor="start" class="axis" style="fill:#7e22ce;font-weight:600">Plateau K=1</text>')
    parts.append(f'<text x="{x0 + pw/2:.1f}" y="{y0 + ph + 16}" text-anchor="middle" class="axis">log10(t) ({lt_min:.1f} .. {lt_max:.1f})</text>')

    parts.append('</svg>')
    out_dir = os.path.dirname(out_path)
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
    with open(out_path, 'w') as f:
        f.write('\n'.join(parts))


def main():
    parser = argparse.ArgumentParser(description="Visualize Hermitian slice eigenvalues from tensor-sieve CSV output.")
    parser.add_argument('--csv', default=None, help="Path to CSV output from cmd/Main.lean (default: data/data.csv or data.csv)")
    parser.add_argument('--max-dim', type=int, default=(64 if HAS_NUMPY else 36),
                        help="Maximum slice dimension to diagonalize")
    parser.add_argument('--out', default=None, help="Output path (.png with matplotlib, or .svg fallback)")
    args = parser.parse_args()

    csv_path = args.csv
    if csv_path is None:
        csv_path = 'data/data.csv' if os.path.exists('data/data.csv') else 'data.csv'
    if not os.path.exists(csv_path):
        print("Data file not found. Run `lake exe tensor_sieve > data/data.csv` first.")
        sys.exit(1)

    slices = load_slices(csv_path)
    if not slices:
        print(f"No valid (level, x, ...) rows found in {csv_path}.")
        sys.exit(1)

    best_lvl = max(slices.keys(), key=lambda lv: (len(slices[lv]), lv))
    nodes = slices[best_lvl][:args.max_dim]

    H, _, _ = build_slice_operators(nodes)
    n = len(nodes)
    herm_err = max(abs(H[i][j] - H[j][i].conjugate()) for i in range(n) for j in range(n))
    eigs = hermitian_eigenvalues(H)
    unfolded, spacings = unfold_bulk_spacings(eigs)
    mean_s = sum(spacings) / len(spacings) if spacings else 1.0
    s_norm = [s / mean_s for s in spacings]
    r_val = adjacent_spacing_ratio(unfolded)
    t_vals, k_vals = compute_sff(unfolded)

    sorted_levels = sorted(slices.keys(), reverse=True)
    level_traces = [sum(parity_sign(x) * count_factors(x) for x in slices[lv]) for lv in sorted_levels]

    print(
        f"Loaded {len(slices)} levels from {csv_path}. "
        f"Selected level Ω={best_lvl} (dim={len(nodes)}, ||H - H*||_inf={herm_err:.2e}, <r>={r_val:.4f})."
    )

    if HAS_MATPLOTLIB:
        out_plot = args.out or 'assets/spectrum_visualization.png'
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        ax1, ax2, ax3, ax4 = axes[0, 0], axes[0, 1], axes[1, 0], axes[1, 1]

        x_pos = list(range(len(sorted_levels)))
        colors = ['#2ca02c' if v >= 0 else '#ff7f0e' for v in level_traces]
        ax1.bar(x_pos, level_traces, color=colors, edgecolor='black', alpha=0.8)
        ax1.axhline(0, color='black', linewidth=0.8)
        ax1.set_xticks(x_pos)
        ax1.set_xticklabels([f"Ω={lv}" for lv in sorted_levels], rotation=45, ha='right')
        ax1.set_title('Diagonal Trace Signature by Factor-Weight Level')
        ax1.set_xlabel('Horizontal Slice Level (Ω)')
        ax1.set_ylabel('Tr(H_slice) = (-1)^Ω · Ω · |slice|')
        ax1.grid(True, axis='y', alpha=0.4)

        ax2.step(eigs, list(range(1, len(eigs) + 1)), where='post', color='teal', linewidth=2)
        ax2.set_title(f'Exact Eigenvalue Staircase (Level Ω={best_lvl}, d={len(nodes)})')
        ax2.set_xlabel('Eigenvalue λ (Hermitian sliceMatrix H)')
        ax2.set_ylabel('Cumulative Count N(λ)')
        ax2.grid(True, alpha=0.4)

        if s_norm:
            bins_count = max(8, min(20, len(s_norm) // 2))
            ax3.hist(s_norm, bins=bins_count, density=True, alpha=0.65,
                     color='steelblue', edgecolor='black', label=f'Slice H (<r>={r_val:.3f})')
            s_max = max(3.0, max(s_norm) * 1.1)
            s_vals = [s_max * i / 249.0 for i in range(250)]
            ax3.plot(s_vals, [math.exp(-s) for s in s_vals], 'k--', linewidth=1.4, label='Poisson (<r>=0.386)')
            ax3.plot(s_vals, [(math.pi / 2.0) * s * math.exp(-(math.pi / 4.0) * s * s) for s in s_vals],
                     color='darkorange', linestyle='-.', linewidth=1.6, label='GOE (<r>=0.531)')
            ax3.plot(s_vals, [(32.0 / math.pi**2) * s * s * math.exp(-(4.0 / math.pi) * s * s) for s in s_vals],
                     'r-', linewidth=2.0, label='GUE (<r>=0.600)')
            ax3.legend(fontsize=9)
        ax3.set_title('Normalized Eigenvalue Spacing Distribution')
        ax3.set_xlabel('Normalized Unfolded Spacing (s)')
        ax3.set_ylabel('Probability Density P(s)')
        ax3.grid(True, alpha=0.4)

        ax4.loglog(t_vals, k_vals, color='black', linewidth=1.3, label='Single-slice K(t)')
        ax4.axhline(1.0, color='purple', linestyle='--', alpha=0.6, label='Asymptotic Plateau (K=1)')
        ax4.legend(fontsize=9)
        ax4.set_title('Spectral Form Factor K(t) (Unfolded Eigenvalues)')
        ax4.set_xlabel('Time (t)')
        ax4.set_ylabel('K(t)')
        ax4.grid(True, which='both', alpha=0.35)

        plt.tight_layout()
        out_dir = os.path.dirname(out_plot)
        if out_dir:
            os.makedirs(out_dir, exist_ok=True)
        plt.savefig(out_plot, dpi=150)
        print(f"Saved Matplotlib visualization to {out_plot}")
    else:
        out_svg = args.out or 'assets/spectrum_visualization.svg'
        save_svg_plot(out_svg, sorted_levels, level_traces, best_lvl, nodes, eigs, s_norm, r_val, t_vals, k_vals)
        print(f"Matplotlib not installed; saved zero-dependency vector visualization to {out_svg}")


if __name__ == '__main__':
    main()
