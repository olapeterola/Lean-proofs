/-
Copyright (c) 2026 Peter Olanipekun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Olanipekun
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory MeasureTheory.Measure

/-- The Hermite-Hadamard inequality: for a convex function f on [a,b],
    f((a+b)/2) ≤ (1/(b-a)) ∫_a^b f(x) dx ≤ (f(a)+f(b))/2 -/
theorem hermite_hadamard {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hfc : ContinuousOn f (Set.Icc a b)) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  have hab' : b - a ≠ 0 := by linarith
  have hab'' : (0 : ℝ) < b - a := by linarith
  have hle : a ≤ b := le_of_lt hab
  have hIcc_closed : IsClosed (Set.Icc a b) := isClosed_Icc (a := a) (b := b)
  have hf_intOn : IntegrableOn f (Set.Icc a b) volume := hfc.integrableOn_Icc
  have hf_int : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hle]
  have hμIcc_pos : 0 < volume (Set.Icc a b) := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_pos.mpr hab''
  have hμIcc_finite : volume (Set.Icc a b) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hμIcc_real : (volume (Set.Icc a b)).toReal = b - a := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (le_of_lt hab'')]
  constructor
  · -- Left inequality: f((a+b)/2) ≤ (1/(b-a)) ∫_a^b f(x) dx
    have hJensen : f (⨍ x in Set.Icc a b, x) ≤ ⨍ x in Set.Icc a b, f x :=
      hf.map_set_average_le hfc hIcc_closed
        hμIcc_pos.ne' hμIcc_finite.ne
        (ae_restrict_mem measurableSet_Icc)
        continuous_id.continuousOn.integrableOn_Icc
        hf_intOn
    have hmid : ⨍ x in Set.Icc a b, x = (a + b) / 2 := by
      simp only [average_eq, measureReal_def]
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hμIcc_real,
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
          integral_id]
      simp only [smul_eq_mul]
      field_simp
      ring
    have havg : ⨍ x in Set.Icc a b, f x =
        (1 / (b - a)) * ∫ x in a..b, f x := by
      simp only [average_eq, measureReal_def]
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hμIcc_real,
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
      simp only [smul_eq_mul]
      field_simp
    linarith [hmid ▸ hJensen, havg ▸ hJensen]
  · -- Right inequality: (1/(b-a)) ∫_a^b f(x) dx ≤ (f(a)+f(b))/2
    have hconv_param : ∀ t ∈ Set.Icc (0:ℝ) 1,
        f ((1 - t) * a + t * b) ≤ (1 - t) * f a + t * f b := by
      intro t ht
      have ht0 : (0:ℝ) ≤ t := ht.1
      have ht1 : t ≤ (1:ℝ) := ht.2
      have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hle
      have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hle
      have h := hf.2 ha_mem hb_mem
        (show 0 ≤ 1 - t by linarith)
        (show 0 ≤ t by linarith)
        (show (1 - t) + t = 1 by ring)
      simp only [smul_eq_mul] at h
      linarith [h]
    have h_aff_cont : ContinuousOn (fun t : ℝ => (1 - t) * a + t * b) (Set.Icc 0 1) :=
      (by continuity : Continuous fun t : ℝ => (1 - t) * a + t * b).continuousOn
    have h_aff_maps : Set.MapsTo (fun t : ℝ => (1 - t) * a + t * b)
        (Set.Icc 0 1) (Set.Icc a b) := by
      intro t ht; constructor <;> nlinarith [ht.1, ht.2]
    have hfcomp_cont : ContinuousOn (fun t => f ((1 - t) * a + t * b)) (Set.Icc 0 1) :=
      hfc.comp h_aff_cont h_aff_maps
    have hfcomp_int : IntervalIntegrable (fun t => f ((1 - t) * a + t * b)) volume 0 1 :=
      hfcomp_cont.intervalIntegrable_of_Icc (by norm_num)
    have hlin_int : IntervalIntegrable (fun t => (1 - t) * f a + t * f b) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); fun_prop
    have hconv_int : ∫ t in (0:ℝ)..1, f ((1 - t) * a + t * b) ≤
        ∫ t in (0:ℝ)..1, ((1 - t) * f a + t * f b) :=
      intervalIntegral.integral_mono_on (by norm_num) hfcomp_int hlin_int
        (fun t ht => hconv_param t ht)
    have hrhs : ∫ t in (0:ℝ)..1, ((1 - t) * f a + t * f b) = (f a + f b) / 2 := by
      have hrewrite : ∫ t in (0:ℝ)..1, ((1 - t) * f a + t * f b) =
          ∫ t in (0:ℝ)..1, (f a + (f b - f a) * t) := by
        congr 1; ext t; ring
      rw [hrewrite, intervalIntegral.integral_add
            (by apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); fun_prop)
            (by apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); fun_prop),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      have hI : ∫ t in (0:ℝ)..1, t = (1:ℝ) / 2 := by rw [integral_id]; norm_num
      rw [hI]; norm_num; ring
    have hsubst : ∫ t in (0:ℝ)..1, f ((1 - t) * a + t * b) =
        (1 / (b - a)) * ∫ x in a..b, f x := by
      have heq : ∀ t : ℝ, (1 - t) * a + t * b = a + (b - a) * t := fun t => by ring
      simp_rw [heq]
      have h := intervalIntegral.integral_comp_add_mul
        (f := f) (a := (0:ℝ)) (b := 1) (c := b - a) hab' a
      simp only [mul_zero, add_zero, mul_one] at h
      rw [h]
      simp only [smul_eq_mul]
      have : a + (b - a) = b := by ring
      rw [this]
      field_simp
    linarith [hsubst ▸ hconv_int]
