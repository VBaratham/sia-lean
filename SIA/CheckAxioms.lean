/-
  SIA.CheckAxioms — Compile-time verification that no classical axioms are used

  Uses `#print axioms` style checking to verify all SIA declarations
  are free of Classical.choice.
-/
import SIA.Delta
import SIA.Continuity
import SIA.Derivative

-- Spot-check key theorems: if any uses Classical.choice, the build will show it.
-- Run `lake build` and inspect output: only `propext` and `Quot.sound` should appear.

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
