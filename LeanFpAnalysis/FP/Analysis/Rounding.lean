-- Rounding.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import LeanFpAnalysis.FP.Model

namespace LeanFpAnalysis.FP

/-!
# Accumulated Rounding Error Bound (γ)

Following Higham, "Accuracy and Stability of Numerical Algorithms", §3.1.

For a sequence of n elementary floating-point operations each introducing
a relative error at most u (the unit roundoff), the worst-case accumulated
relative error is bounded by γ(n), defined below.

The definition is valid only under the side condition `n * u < 1`,
which ensures the denominator is positive and the bound is finite.
This condition is always satisfied in practice for reasonable n,
since u is of order 2⁻⁵³ for IEEE double precision.
-/

-- ============================================================
-- §3.1  The γ function
-- ============================================================

/-- `gamma fp n` is Higham's γₙ = (n * u) / (1 - n * u).

    It bounds the relative error accumulated after n rounding operations,
    each satisfying the standard model fl(x op y) = (x op y)(1 + δ), |δ| ≤ u.

    Precondition for meaningful use: `n * fp.u < 1`.
    See `gammaValid` for the explicit guard and `prod_error_bound` for the
    central lemma that justifies this bound. -/
noncomputable def gamma (fp : FPModel) (n : ℕ) : ℝ :=
  (n * fp.u) / (1 - n * fp.u)

/-- Well-definedness guard for `gamma`.
    The denominator `1 - n * u` is positive iff `n * u < 1`.
    All lemmas that use `gamma` in a meaningful bound require this hypothesis.
    In practice this holds for any realistic algorithm depth, since
    u ≈ 2⁻⁵³ in double precision. -/
def gammaValid (fp : FPModel) (n : ℕ) : Prop :=
  (n : ℝ) * fp.u < 1

-- ============================================================
-- §3.1  Product lemma
-- ============================================================

open scoped BigOperators

/-- **Product rounding error lemma** (Higham §3.1, Lemma 3.1).

    Given n rounding errors δ_i with |δ_i| ≤ u, their product satisfies
      ∏ᵢ (1 + δᵢ) = 1 + θ
    for some θ with |θ| ≤ γ(n).

    This is the foundational lemma for all forward error analysis:
    any composition of n rounded operations accumulates a relative
    error bounded by γ(n), regardless of the signs of the individual δᵢ.

    Proof sketch (induction on n):
      Base: n = 0, product is 1, θ = 0, trivial.
      Step: assume ∏ᵢ<n (1 + δᵢ) = 1 + θ' with |θ'| ≤ γ(n).
        Then ∏ᵢ<n+1 (1 + δᵢ) = (1 + θ')(1 + δₙ) = 1 + (θ' + δₙ + θ'δₙ).
        Set θ = θ' + δₙ + θ'δₙ, bound |θ| using
          |θ| ≤ (γ(n) + u + γ(n)*u) = γ(n+1). -/
lemma prod_error_bound (fp : FPModel) (n : ℕ) (δ : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hn : gammaValid fp n) :
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      ∏ i : Fin n, (1 + δ i) = 1 + θ := by
  sorry

end LeanFpAnalysis.FP
