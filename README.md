# tensor-sieve

`tensor-sieve` is a Lean 4 formalization library and Python diagnostic suite for finite-dimensional Krein-space ($J$-self-adjoint) operators, prime-step graph trace identities, and discrete spectral statistics. It serves as the formal algebraic counterpart to the browser workbench [krein](https://github.com/ryanncode/krein).

## Project Layout

- **`TensorSieve/` and `PTSymmetry/` (Verified Lean 4 Core):** Compiles under Lean `v4.32.0` with zero `sorry` placeholders and zero custom axioms; every core theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **`TensorSieve/Speculative/` (Archived Exploratory Sketches):** Unproven research stubs (`CondensedMath.lean`, `TopologicalPeriodicCyclicHomology.lean`, `AdelicBridge.lean`, `TatesThesis.lean`) kept out of the main build (`TensorSieve.lean` does not import them).
- **`scripts/` (Numerical Diagnostics):** Standalone Python tools for spectral spacing tests against random-matrix null models (`adelic_operator_probe.py`), Hermitian slice diagonalization plots from `cmd/Main.lean` output (`visualize_spectrum.py`), and independent Weil explicit-formula benchmarks (`verify_riemann_zeros.py`).

## Verified Lean 4 Modules

| Module | Proved Results |
|---|---|
| [TensorSieve/Operator.lean](TensorSieve/Operator.lean) | Symmetry of the $p$-adic $L^1$ distance `valuationDivergence`; conjugate symmetry of `crossBranchAmplitude`; Hermiticity of the slice coherence matrix (`sliceMatrix_isHermitian`, $H^* = H$); `sliceJ_sq` ($J^2 = I$); `sliceKreinOperator_isJAdjoint` ($JC = C^*J$); and `krein_eigenvalue_real_of_non_isotropic` (every eigenvector with nonzero Krein inner product $[v, v]_J \ne 0$ has a real eigenvalue). |
| [TensorSieve/KreinBridge.lean](TensorSieve/KreinBridge.lean) | Connects the abstract `PTSymmetry` Krein-space classes (`IndefiniteMetric`, `KreinSpace`, `HasJOperator`, `MajorantPositiveDefinite`, `IsJAdjoint`) to concrete finite-dimensional slice spaces `SliceVec slice := Fin slice.length → ℝ`, proving exact agreement with the real part of `sliceKreinOperator`. |
| [TensorSieve/DiscreteTrace.lean](TensorSieve/DiscreteTrace.lean) | Proves an abstract finite-graph trace decomposition and discharges all hypotheses unconditionally for prime-step graphs in `concrete_prime_step_selberg_trace`: $\mathrm{Tr}(L_c^2) = \mathrm{Tr}(D^2) + \sum_{p \in P} \sum_{x \in S} \deg_p(x, S)$. Also defines general walk-length matrix powers `matrixPow` and traces `discreteTracePow`. |
| [TensorSieve/Kinematics.lean](TensorSieve/Kinematics.lean) | Well-founded divisibility ordering on positive integers and `kinematicSieve_eq_one` (minimal-prime descent terminates cleanly at `1` for every positive integer). |
| [TensorSieve/LambdaRing.lean](TensorSieve/LambdaRing.lean) & [F1Descent.lean](TensorSieve/F1Descent.lean) | Instantiates Borger's Frobenius-lift $\Lambda$-ring structure on $\mathbb{Z}$ via Fermat's Little Theorem (`ZMod.pow_card`) and proves Adams ring-homomorphism properties. |
| [TensorSieve/PunctureMask.lean](TensorSieve/PunctureMask.lean) & [Theorem.lean](TensorSieve/Theorem.lean) | Coprimality indicator gates, Möbius inversion expansion, symmetric $p$-adic $L^1$ tree metric on `SemanticAddress`, prime-division factor drop (`countFactors_div_prime`), closed-form uniform-weight trace (`traceHamiltonian_of_uniform_weight`), and proof that single constant-weight slices have scalar symmetry $J = (-1)^k I$ and Hermitian `sliceKreinOperator`. |
| [TensorSieve/FTNILO.lean](TensorSieve/FTNILO.lean) & [GaloisRepresentation.lean](TensorSieve/GaloisRepresentation.lean) | Integer indicator gates (`diracDeltaGate`), exact matrix-multiplication equivalence for finite contractions (`leftToRightContraction_eq_mul`, `halfPartialTrace_eq_sum`), and Krein-isometric group representations (`G : Type*` with `[Group G]` acting by indefinite-metric isometries). |
| [PTSymmetry/](PTSymmetry/) | Standalone indefinite-metric Krein-space package covering Minkowski signature validation (`Minkowski.lean`), fundamental symmetry $J$, the induced positive-definite Majorant Hilbert space (`MajorantTopology.lean`), cone projections (`P_plus_add_P_minus`), Gupta–Bleuler physical subspaces, and $J$-self-adjoint Hamiltonians. |

## Building and Running Tests

Always fetch the prebuilt Mathlib binary cache before compiling:

```bash
lake exe cache get
lake build TensorSieve PTSymmetry
lake env lean --run tests/Tests.lean
```

`tests/Tests.lean` runs all `#guard` checks and prints the exact axiom list (`#print axioms`) for the core theorems.

## Numerical Diagnostics

### 1. Operator Spacing & Null-Model Probe (`scripts/adelic_operator_probe.py`)

Runs with zero external Python dependencies (pure standard library, with an automatic NumPy fast path if installed). It computes the unfolding-free adjacent spacing ratio $\langle r \rangle = \langle \min(s_n, s_{n+1}) / \max(s_n, s_{n+1}) \rangle$ (benchmarks: Poisson `0.3863`, GOE `0.5307`, GUE `0.5996`) and compares discrete arithmetic operators against random-matrix null models of the same dimension:

```bash
python3 scripts/adelic_operator_probe.py --max-dim 24 --trials 6
```

Three concrete structural observations emerge on finite slices ($d \le 24$):
1. **Constant parity on single horizontal slices:** Every integer in a single downward slice shares the same $\Omega(x)$, so $J = \pm I$ and $C = \pm H$ is Hermitian with purely real eigenvalues. On the largest slice of `510510` ($d = 24$), the antisymmetric imaginary coupling yields $\langle r \rangle = 0.5946$ (matching the $d = 24$ GUE null control of `0.5962`), whereas the power-heavy slice of `27720` ($d = 22$) sits near GOE at `0.5125`.
2. **Integrability of separable prime-step graphs:** A sparse prime-step divisor graph weighted by von Mangoldt amplitudes $w(p) = \ln p / \sqrt{p}$ factors as a Cartesian product of one-dimensional chains across primes. Even with a time-reversal-breaking Peierls magnetic phase, its spectrum obeys Berry–Tabor Poisson statistics ($\langle r \rangle \in [0.25, 0.41]$). Generating GUE level repulsion requires coupling distinct primes non-separably (for example, through additive order $a > b$).
3. **Broken-PT complex pairs on mixed-level slices:** Combining two adjacent levels creates a genuinely indefinite signature (such as $(12+, 12-)$). The operator $C = JH$ maintains exact $J$-self-adjointness ($\|JC - C^*J\|_\infty = 0$) while splitting 20–22 of its 24 eigenvalues into complex conjugate pairs supported on isotropic eigenvectors, matching `krein_eigenvalue_real_of_non_isotropic`.

### 2. Weil Explicit-Formula Benchmark (`scripts/verify_riemann_zeros.py`)

Evaluates the classical Gaussian-damped Weil explicit-formula cosine sum over prime powers $u = \ln(p^k)$ weighted by $(\ln p / p^{k/2}) e^{-\frac{1}{2}(\sigma u)^2}$. This script is independent of the slice matrices above and provides a fast numerical check against LMFDB values for $\gamma_1 \dots \gamma_{10}$ (mean relative error below `0.25%` at prime cutoff `1000`):

```bash
python3 scripts/verify_riemann_zeros.py --primorial 1000 --num-zeros 10
```

![Riemann Zero Resonance Spectrum](assets/zeros_resonance.png)
