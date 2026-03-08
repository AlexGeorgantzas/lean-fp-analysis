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

end LeanFpAnalysis.FP
