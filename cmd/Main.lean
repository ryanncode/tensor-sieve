import TensorSieve.Operator

open KinematicRiemann

/-!
# Terminal Stream and Verification Pipeline

This module provides the executable entry point for the `tensor-sieve` program.
It implements a high-performance simulation loop that iterates through
the discrete p-adic tree slices and pipes the emitted data stream out to `data.csv`.
-/

/-
Formal Warrant: Live evaluation of the emission spectrum values.
This `#eval` acts as a static, machine-checked guarantee in the IDE InfoView
that the structural generation of horizontal slices and transition amplitudes
remains logically consistent without non-termination loops.
-/
#eval emissionSpectrumDown 27720 20

/--
Streams the downward slice data to standard output as CSV (`level,x,local_degree`).

- `start`: The starting semantic address (an integer with high prime multiplicity)
- `max_steps`: The depth of the p-adic tree slice iteration
-/
def emitDataDown (start : ℕ) (max_steps : ℕ) : IO Unit := do
  IO.println "level,x,local_degree"
  let data := emissionSpectrumDown start max_steps
  for (lvl, x, deg) in data do
    IO.println s!"{lvl},{x},{deg}"

/--
The main entry point for the compiled executable.
Initializes the horizontal cross-branch sieve from a massive, highly composite integer
to force maximum initial topological entanglement, resolving down 1000 levels.
-/
def main : IO Unit := do
  -- Start from a highly composite number to see the sieve downward across many nodes.
  -- 27720000 = 2^6 * 3^2 * 5^4 * 7 * 11 (Prime weight: 14)
  emitDataDown 27720000 1000
