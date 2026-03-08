-- Algorithms/DotProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.Summation

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point dot product of two n-dimensional vectors.

    Models the standard sequential accumulation:
      acc₀     = 0
      accᵢ₊₁  = fl_add accᵢ (fl_mul (x i) (y i))

    Each step introduces up to two rounding errors (one from fl_mul,
    one from fl_add), giving 2n total rounding operations for an
    n-dimensional dot product. -/
noncomputable def fl_dotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0

/-- **Dot product rounding error bound** (Higham §3.5).

    The computed floating-point dot product satisfies:
      |fl_dotProduct fp x y - ∑ i, x i * y i| ≤ γ(2n) * ∑ i, |x i| * |y i|

    Proof sketch:
      1. Apply model_mul to each fl_mul (x i) (y i), yielding n terms
         (x i * y i)(1 + δᵢ) with |δᵢ| ≤ u.
      2. Apply fl_sum_error to the accumulated additions.
      3. Combine both sources (n muls + n adds = 2n ops) via prod_error_bound
         to obtain the γ(2n) bound. -/
theorem dotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp (2 * n) * ∑ i : Fin n, |x i| * |y i| := by
  sorry

end LeanFpAnalysis.FP
