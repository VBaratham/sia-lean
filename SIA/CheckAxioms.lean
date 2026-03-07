/-
  SIA.CheckAxioms — Compile-time verification that no classical axioms are used

  Uses `#print axioms` style checking to verify all SIA declarations
  are free of Classical.choice.
-/
import SIA.Delta
import SIA.Continuity
import SIA.Derivative
import SIA.HigherOrder
import SIA.Integration
import SIA.FTC

-- Spot-check key theorems: if any uses Classical.choice, the build will show it.
-- Run `lake build` and inspect output: only `propext` should appear.

#print axioms SIA.not_lem_on_delta
#print axioms SIA.delta_nondegenerate
#print axioms SIA.delta_indistinguishable_zero
#print axioms SIA.microcancellation
#print axioms SIA.microaffinity
#print axioms SIA.delta_not_microstable
#print axioms SIA.all_continuous
#print axioms SIA.deriv_add_slope
#print axioms SIA.deriv_mul_slope
#print axioms SIA.deriv_comp_slope
#print axioms SIA.deriv_neg_slope
#print axioms SIA.deriv_add_eq
#print axioms SIA.deriv_mul_eq
#print axioms SIA.deriv_comp_eq
#print axioms SIA.neighbors_not_transitive

-- HigherOrder
#print axioms SIA.delta_in_delta_k

-- Integration
#print axioms SIA.antideriv_unique
#print axioms SIA.ftc_part2
#print axioms SIA.shift_is_antideriv
#print axioms SIA.ftc_part1
#print axioms SIA.zero_slope_is_zero
#print axioms SIA.zero_slope_is_const
#print axioms SIA.antideriv_add
#print axioms SIA.antideriv_const_mul
#print axioms SIA.antideriv_neg
#print axioms SIA.antideriv_sub
#print axioms SIA.integral_additive
#print axioms SIA.antideriv_slope_eq

-- FTC
#print axioms SIA.ftc1
#print axioms SIA.ftc2
#print axioms SIA.integral_well_defined
#print axioms SIA.same_deriv_differ_by_const
#print axioms SIA.eq_of_same_deriv_and_initial
#print axioms SIA.integration_by_parts
