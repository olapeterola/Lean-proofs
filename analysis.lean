import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

/-- The Hermite-Hadamard inequality for convex functions -/
theorem hermite_hadamard {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hfc : ContinuousOn f (Set.Icc a b)) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  sorry
