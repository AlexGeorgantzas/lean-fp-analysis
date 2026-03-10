-- Error.lean

import Mathlib.Data.Real.Basic

namespace LeanFpAnalysis.FP

/-!
# Floating-Point Error Measures

Following Higham, "Accuracy and Stability of Numerical Algorithms", Ch. 1.
We define absolute error and relative error as the standard measures of
floating-point approximation quality.
-/

-- ============================================================
-- §1.2  Error measures
-- ============================================================

/-- Absolute error of a floating-point approximation.
    Defined as |computed - exact|. No assumption on exact. -/
noncomputable def absError (computed exact : ℝ) : ℝ :=
  |computed - exact|

/-- Relative error of a floating-point approximation.
    Defined as |computed - exact| / |exact|.
    Meaningful only when `exact ≠ 0`; the caller must enforce this. -/
noncomputable def relError (computed exact : ℝ) : ℝ :=
  |computed - exact| / |exact|

-- ============================================================
-- §1.2  Componentwise relative error (for vectors)
-- ============================================================

/-- Componentwise relative error bound for a computed vector approximation.

    Asserts that every component's relative error is at most ε:
      ∀ i, |computed_i - exact_i| / |exact_i| ≤ ε

    This is the form most directly usable in error-bound lemmas.
    Requires all exact components to be nonzero; the caller must enforce this. -/
def compRelErrorBounded (n : ℕ) (computed exact : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ i : Fin n, relError (computed i) (exact i) ≤ ε

-- ============================================================
-- §1.7  Backward error
-- ============================================================

/-- Backward error bound for a computed result `xhat` for problem `f` with input `a`.

    Asserts that there exists a perturbation Δa with |Δa| ≤ ε such that `xhat` is
    the *exact* solution to the perturbed problem `f(a + Δa)`:
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat

    This is the form most directly usable in stability proofs.
    The scalar case; vector problems are handled in Stability.lean. -/
def backwardErrorBounded (f : ℝ → ℝ) (a xhat ε : ℝ) : Prop :=
  ∃ Δa : ℝ, |Δa| ≤ ε ∧ f (a + Δa) = xhat

end LeanFpAnalysis.FP
