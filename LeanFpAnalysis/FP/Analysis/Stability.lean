-- Stability.lean

import Mathlib.Data.Real.Basic
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error

namespace LeanFpAnalysis.FP

/-!
# Stability and Condition Number

Following Higham, "Accuracy and Stability of Numerical Algorithms", §1.7–§1.9.

We formalise the key concepts that classify how well an algorithm handles
the unavoidable rounding errors introduced by finite precision arithmetic:
backward stability and the condition number of a problem.
-/

-- ============================================================
-- §1.7  Backward stability (scalar problems)
-- ============================================================

/-- An algorithm computing `f : ℝ → ℝ` at input `a` is **backward stable**
    if the computed result `xhat` is the exact answer for a slightly perturbed
    input.  The perturbation is required to be no larger than `ε`:
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat

    Typically ε is taken proportional to the unit roundoff u, e.g., ε = c * u
    for a small constant c depending on the algorithm.

    See `backwardErrorBounded` in Error.lean for the underlying predicate. -/
def isBackwardStable (fp : FPModel) (f : ℝ → ℝ) (alg : ℝ → ℝ)
    (c : ℝ) : Prop :=
  ∀ a : ℝ, backwardErrorBounded f a (alg a) (c * fp.u)

-- ============================================================
-- §1.7  Backward stability (vector problems)
-- ============================================================

/-- Backward stability for a vector-to-vector problem `f : (Fin n → ℝ) → (Fin m → ℝ)`.

    The computed output `alg a` is the exact answer for a componentwise-perturbed
    input: each input component `a_i` is perturbed by at most `ε`:
      ∀ i, ∃ Δaᵢ, |Δaᵢ| ≤ ε ∧ f(a + Δa) = alg a

    Here we require a *single* Δa vector whose max componentwise perturbation is ε. -/
def isVectorBackwardStable (fp : FPModel) (n m : ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (alg : (Fin n → ℝ) → (Fin m → ℝ))
    (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    ∃ Δa : Fin n → ℝ,
      (∀ i, |Δa i| ≤ c * fp.u) ∧
      f (fun i => a i + Δa i) = alg a

-- ============================================================
-- §1.9  Condition number of a scalar problem
-- ============================================================

/-- The condition number of a differentiable scalar problem `f` at input `a`.

    Defined as the relative change in output per unit relative change in input:
      κ(f, a) = |a * f'(a) / f(a)|

    A large condition number means the problem is ill-conditioned: small relative
    changes in input cause large relative changes in output, independently of
    the algorithm used.

    The derivative `f'` must be supplied by the caller (as a function `df`).
    Meaningful only when `f(a) ≠ 0`; the caller must enforce this. -/
noncomputable def condNumber (f df : ℝ → ℝ) (a : ℝ) : ℝ :=
  |a * df a / f a|

/-- A problem `f` is **well-conditioned** at `a` if its condition number is
    at most `κ_max`.  The threshold `κ_max` is problem- and context-dependent;
    typical values are O(1) to O(1/u) where u is the unit roundoff. -/
def isWellConditioned (f df : ℝ → ℝ) (a κ_max : ℝ) : Prop :=
  condNumber f df a ≤ κ_max

-- ============================================================
-- §1.7  Forward error from backward error + condition number
-- ============================================================

/-- **Fundamental theorem of backward error analysis** (Higham §1.7).

    If an algorithm is backward stable (backward error ≤ ε) and the problem has
    condition number κ, then the forward relative error satisfies:
      |f(a) - alg(a)| / |f(a)| ≲ κ * ε

    This is stated as a sorry'd lemma; the proof requires differentiability of f
    and a linearisation argument.

    Proof sketch: f(a + Δa) = alg(a) with |Δa| ≤ ε, so
      |f(a) - alg(a)| = |f(a) - f(a + Δa)| ≈ |f'(a)| * |Δa|
                      ≤ |f'(a)| * ε = κ(f,a) * (ε / |a|) * |f(a)|. -/
lemma forward_from_backward (f df : ℝ → ℝ) (a ε : ℝ)
    (hf : f a ≠ 0)
    (hback : backwardErrorBounded f a (f a) ε) :
    |f a - f a| / |f a| ≤ condNumber f df a * ε := by
  sorry

end LeanFpAnalysis.FP
