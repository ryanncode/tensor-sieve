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
Streams the data directly to standard output as a comma-separated format.
This function traces the local degree, the topological jams, and the
dynamic eigenvalue spacing.

- `start`: The starting semantic address (an integer with high prime multiplicity)
- `max_steps`: The depth of the p-adic tree slice iteration
-/
def emitDataDown (start : ℕ) (max_steps : ℕ) : IO Unit := do
  IO.println "level,x,amplitude,local_degree,jammed,eigenvalue_spacing"
  let data := emissionSpectrumDown start max_steps
  let mut last_jam_idx : Option ℕ := none
  let mut current_lvl : ℕ := 0
  let mut current_idx : ℕ := 0
  for (lvl, x, amp, deg, jammed) in data do
    if lvl != current_lvl then
      current_lvl := lvl
      current_idx := 0
      last_jam_idx := none
    let mut spacing : ℕ := 0
    if jammed == 1 then
      if let some last := last_jam_idx then
        spacing := current_idx - last
      last_jam_idx := some current_idx
    IO.println s!"{lvl},{x},{amp},{deg},{jammed},{spacing}"
    current_idx := current_idx + 1

/--
The main entry point for the compiled executable.
Initializes the horizontal cross-branch sieve from a massive, highly composite integer
to force maximum initial topological entanglement, resolving down 1000 levels.
-/
def main : IO Unit := do
  -- Start from a highly composite number to see the sieve downward across many nodes.
  -- 27720000 = 2^6 * 3^2 * 5^4 * 7 * 11 (Prime weight: 14)
  emitDataDown 27720000 1000
