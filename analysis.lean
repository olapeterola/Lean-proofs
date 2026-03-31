import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

/-- The Hermite-Hadamard inequality for convex functions -/
theorem hermite_hadamard {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hfc : ContinuousOn f (Set.Icc a b)) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  constructor
  · have hab' : b - a ≠ 0 := by linarith
    have hIcc_ne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt hab)
    have hIcc_closed : IsClosed (Set.Icc a b) := isClosed_Icc (a := a) (b := b)
    have hconv : ConvexOn ℝ (Set.Icc a b) f := hf
    have hmid : (a + b) / 2 ∈ Set.Icc a b := by
      constructor
      · linarith
      · linarith
    have hf_int : IntervalIntegrable f MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le (le_of_lt hab)]
    have hf_intOn : IntegrableOn f (Set.Icc a b) MeasureTheory.volume := by
      apply ContinuousOn.integrableOn_Icc hfc
    sorry
  · sorry
