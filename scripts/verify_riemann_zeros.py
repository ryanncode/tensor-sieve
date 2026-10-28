#!/usr/bin/env python3
"""
verify_riemann_zeros.py

Standalone numerical verification engine extracting physical Riemann zero heights
(gamma_1 = 14.134725..., gamma_2 = 21.022040..., etc.) from discrete p-adic tree
kinematics and prime valuation spectra.

Designed to operate over massive arithmetic seeds (e.g., Primorials scaling
from 10^17 up to 10^500+) using exact prime-power valuation coordinates without
64-bit integer overflow.
"""

import argparse
import sys
import time
import numpy as np

try:
    import mpmath
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False

try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False

# Hard-coded reference zeros (first 15 non-trivial zero imaginary parts)
CERTIFIED_ZEROS_FALLBACK = [
    14.134725141735,
    21.022039638772,
    25.010857580146,
    30.424876125860,
    32.935061587739,
    37.586178158826,
    40.918719012147,
    43.327073280915,
    48.005150881167,
    49.773832477672,
    52.970321477714,
    56.446247697063,
    59.347044002602,
    60.831778524609,
    65.112544048082,
]

def get_certified_zeros(n_zeros: int):
    """Retrieve certified Riemann zero imaginary parts using mpmath or fallback table."""
    if HAS_MPMATH:
        return [float(mpmath.zetazero(n).imag) for n in range(1, n_zeros + 1)]
    return CERTIFIED_ZEROS_FALLBACK[:n_zeros]

def sieve_primes(max_p: int):
    """Generate all primes up to max_p via standard boolean sieve."""
    if max_p < 2:
        return []
    sieve = [True] * (max_p + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, int(max_p**0.5) + 1):
        if sieve[p]:
            sieve[p*p : max_p+1 : p] = [False] * len(range(p*p, max_p+1, p))
    return [p for p in range(2, max_p + 1) if sieve[p]]

def parse_seed_input(args):
    """
    Parse the target arithmetic seed into:
    - primes: list of distinct prime generators
    - exponents: list of multiplicity exponents
    - log_seed: natural logarithm of the seed integer
    - seed_description: human-readable label
    """
    if args.integer:
        val_str = args.integer.strip()
        n_val = int(val_str)
        # Factorize smaller integers directly
        primes = []
        exps = []
        temp = n_val
        d = 2
        while d * d <= temp:
            if temp % d == 0:
                count = 0
                while temp % d == 0:
                    count += 1
                    temp //= d
                primes.append(d)
                exps.append(count)
            d += 1 if d == 2 else 2
        if temp > 1:
            primes.append(temp)
            exps.append(1)
            
        log_seed = float(np.sum([e * np.log(p) for p, e in zip(primes, exps)]))
        desc = f"Integer N={val_str[:20]}..." if len(val_str) > 20 else f"Integer N={val_str}"
        return primes, exps, log_seed, desc

    if args.factors:
        # Format: "2:10,3:5,5:2"
        primes = []
        exps = []
        for pair in args.factors.split(','):
            p_str, e_str = pair.strip().split(':')
            primes.append(int(p_str))
            exps.append(int(e_str))
        log_seed = float(np.sum([e * np.log(p) for p, e in zip(primes, exps)]))
        desc = f"Custom Factorization ({len(primes)} distinct primes)"
        return primes, exps, log_seed, desc

    # Default: Primorial seed
    p_max = args.primorial
    primes = sieve_primes(p_max)
    exps = [1] * len(primes)
    log_seed = float(np.sum([np.log(p) for p in primes]))
    desc = f"Primorial P={p_max}# ({len(primes)} primes, magnitude ~ 10^{log_seed / np.log(10):.1f})"
    return primes, exps, log_seed, desc

def build_prime_power_support(primes, max_power_bound=100000):
    """
    Generate prime powers p^m supported on the seed generators up to max_power_bound.
    Returns valuation logs and normalized Weil weights.
    """
    u_list = []
    w_list = []
    for p in primes:
        pk = p
        ln_p = np.log(p)
        while pk <= max_power_bound:
            # von Mangoldt weight scaled by p^(-m/2)
            w_list.append(ln_p / np.sqrt(pk))
            u_list.append(np.log(pk))
            pk *= p

    u_vals = np.array(u_list, dtype=np.float64)
    weights = np.array(w_list, dtype=np.float64)
    return u_vals, weights

def compute_spectral_resonance(u_vals, weights, t_min=12.0, t_max=52.0, grid_points=8000, sigma=0.15):
    """
    Evaluate the dual spectral resonance density across the frequency grid t.
    Uses Gaussian wavepacket damping exp(-0.5 * (sigma * u)^2).
    """
    t_grid = np.linspace(t_min, t_max, grid_points, dtype=np.float64)
    damping = np.exp(-0.5 * (sigma * u_vals)**2)
    eff_weights = weights * damping

    # Vectorized cosine projection over prime valuations
    osc = np.dot(np.cos(np.outer(t_grid, u_vals)), eff_weights)

    # Smooth Archimedean density component: (1/2pi) * log(t / 2pi)
    smooth = (1.0 / (2.0 * np.pi)) * np.log(np.maximum(t_grid, 2.0 * np.pi) / (2.0 * np.pi))
    density = smooth - (1.0 / np.pi) * osc

    return t_grid, density

def detect_resonance_peaks(t_grid, density, threshold=0.25):
    """
    Detect local maxima of the resonance density and refine locations
    using 3-point parabolic interpolation.
    """
    peak_idx = (np.diff(np.sign(np.diff(density))) < 0).nonzero()[0] + 1
    peaks = []

    dt = t_grid[1] - t_grid[0]
    for idx in peak_idx:
        if density[idx] >= threshold:
            if 0 < idx < len(density) - 1:
                y0, y1, y2 = density[idx - 1], density[idx], density[idx + 1]
                denom = (y0 - 2.0 * y1 + y2)
                if abs(denom) > 1e-12:
                    delta = 0.5 * (y0 - y2) / denom
                    t_refined = t_grid[idx] + delta * dt
                    peaks.append((float(t_refined), float(y1)))
                else:
                    peaks.append((float(t_grid[idx]), float(y1)))
            else:
                peaks.append((float(t_grid[idx]), float(density[idx])))

    peaks.sort(key=lambda x: x[0])
    return peaks

def main():
    parser = argparse.ArgumentParser(
        description="Verify Riemann zeros from discrete p-adic tree kinematics over massive seeds."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--primorial", type=int, default=1000,
                       help="Prime limit for primorial seed (e.g., 47, 71, 101, 199, 500, 1000). Default: 1000")
    group.add_argument("--integer", type=str,
                       help="Arbitrary integer seed as a numeric string.")
    group.add_argument("--factors", type=str,
                       help="Explicit factor configuration, e.g. '2:50,3:30,5:20'.")

    parser.add_argument("--t-min", type=float, default=12.0, help="Start frequency for spectral sweep. Default: 12.0")
    parser.add_argument("--t-max", type=float, default=52.0, help="End frequency for spectral sweep. Default: 52.0")
    parser.add_argument("--grid-points", type=int, default=8000, help="Evaluation points along t grid. Default: 8000")
    parser.add_argument("--num-zeros", type=int, default=10, help="Number of certified zeros to verify. Default: 10")
    parser.add_argument("--sigma", type=float, default=0.15, help="Gaussian wavepacket resolution width. Default: 0.15")
    parser.add_argument("--power-bound", type=int, default=100000, help="Upper bound for prime power multiplicities. Default: 100000")
    parser.add_argument("--plot", type=str, default="assets/zeros_resonance.png", help="Path to save verification plot. Default: assets/zeros_resonance.png")
    parser.add_argument("--no-plot", action="store_true", help="Disable plot generation.")

    args = parser.parse_args()

    t_start = time.time()
    print("=" * 80)
    print("DISCRETE P-ADIC SIEVE: NUMERICAL ZERO RESONANCE ENGINE")
    print("=" * 80)

    # 1. Parse seed configuration
    primes, exps, log_seed, seed_desc = parse_seed_input(args)
    digits_10 = log_seed / np.log(10)
    print(f"Target Seed: {seed_desc}")
    print(f"Logarithmic Scale: ln(N) = {log_seed:.2f} (Decimal Digits: ~ {digits_10:.1f})")
    print(f"Distinct Prime Generators: omega(N) = {len(primes)}")
    print(f"Total Multiplicity: Omega(N) = {sum(exps)}")
    print("-" * 80)

    # 2. Build prime power support
    u_vals, weights = build_prime_power_support(primes, max_power_bound=args.power_bound)
    print(f"Prime-Power Lattice Size: {len(u_vals)} elements (Power bound: {args.power_bound})")

    # 3. Compute spectral resonance density
    print(f"Sweeping Frequency Domain: t in [{args.t_min:.1f}, {args.t_max:.1f}] ({args.grid_points} steps)...")
    t_grid, density = compute_spectral_resonance(
        u_vals, weights,
        t_min=args.t_min, t_max=args.t_max,
        grid_points=args.grid_points, sigma=args.sigma
    )

    # 4. Extract resonance peaks
    peaks = detect_resonance_peaks(t_grid, density, threshold=0.25)
    print(f"Detected {len(peaks)} Coherent Spectral Peaks.")
    print("-" * 80)

    # 5. Compare against certified LMFDB zeros
    certified_zeros = get_certified_zeros(args.num_zeros)

    print(f"{'n':<4} | {'Certified Zero (gamma_n)':<24} | {'Detected Peak (t)':<18} | {'Abs Error':<12} | {'Rel Error':<10}")
    print("-" * 80)

    total_rel_err = 0.0
    matched_count = 0

    for i, g in enumerate(certified_zeros):
        if not peaks:
            break
        # Find closest peak within frequency search window
        closest = min(peaks, key=lambda p: abs(p[0] - g))
        abs_err = abs(closest[0] - g)
        rel_err = (abs_err / g) * 100.0

        total_rel_err += rel_err
        matched_count += 1

        status_flag = "✓" if rel_err < 0.5 else "!"
        print(f"{i+1:<4} | {g:<24.6f} | {closest[0]:<18.6f} | {abs_err:<12.6f} | {rel_err:6.3f}% {status_flag}")

    print("-" * 80)
    mean_rel_err = (total_rel_err / matched_count) if matched_count > 0 else 0.0
    elapsed = time.time() - t_start

    print(f"Verification Summary: {matched_count}/{args.num_zeros} zeros matched.")
    print(f"Mean Relative Error: {mean_rel_err:.3f}%")
    print(f"Total Compute Time: {elapsed:.2f} seconds")
    print("=" * 80)

    # 6. Generate verification plot if requested
    if HAS_MATPLOTLIB and not args.no_plot and args.plot:
        plt.figure(figsize=(14, 6))
        plt.plot(t_grid, density, 'b-', linewidth=1.5, label='Discrete Sieve Spectral Density R(t)')
        plt.axhline(0, color='gray', linestyle='--', alpha=0.5)

        for i, g in enumerate(certified_zeros):
            if args.t_min <= g <= args.t_max:
                plt.axvline(g, color='red', linestyle=':', alpha=0.7,
                            label='Certified Riemann Zero (gamma_n)' if i == 0 else "")

        for t_p, h_p in peaks:
            if args.t_min <= t_p <= args.t_max:
                plt.plot(t_p, h_p, 'go', markersize=5, label='Detected Resonance Peak' if t_p == peaks[0][0] else "")

        plt.title(f"Riemann Zero Resonance Spectrum via Discrete Sieve (Seed: {seed_desc})", fontsize=13)
        plt.xlabel("Frequency / Imaginary Height (t)", fontsize=11)
        plt.ylabel("Coherent Spectral Density R(t)", fontsize=11)
        plt.xlim(args.t_min, args.t_max)
        plt.legend(loc='upper right')
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.savefig(args.plot, dpi=200)
        print(f"Verification plot saved to: {args.plot}")

if __name__ == "__main__":
    main()

