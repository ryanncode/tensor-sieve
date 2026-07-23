import Mathlib.Data.Complex.Basic
import TensorSieve.Operator
open KinematicRiemann

example : crossBranchAmplitude 4 4 = Complex.mk 2 0 := by norm_num
example : crossBranchAmplitude 8 8 = Complex.mk (-3) 0 := by norm_num
example : crossBranchAmplitude 2 3 = 0 := by norm_num
example : crossBranchAmplitude 12 18 = Complex.mk 0 (-2) := by norm_num
example : crossBranchAmplitude 18 12 = Complex.mk 0 2 := by norm_num
