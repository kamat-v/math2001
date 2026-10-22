/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Midterm project: A Solution -/

/- Step 1. -/

theorem nonneg_or_nonpos_of_mul_nonneg {a b : ℝ} (h : 0 ≤ a * b) : 0 ≤ a ∨ b ≤ 0 := by
  obtain hb1 | hb2 := le_or_gt b 0
  · right
    apply hb1
  · left
    cancel b at h

/- Step 2. -/
example {p k : ℝ} (hk : 0 ≤ k) (h : p ^ 2 ≤ k ^ 2) : -k ≤ p ∧ p ≤ k := by
  have h1 : 0 ≤ (k - p) * (k + p) :=
    calc
      0 ≤ k ^ 2 - p ^ 2 := by addarith [h]
      _ = (k - p) * (k + p) := by ring
  have h2 : 0 ≤ (k + p) * (k - p) :=
    calc
      0 ≤ (k - p) * (k + p) := h1
      _ = (k + p) * (k - p) := by ring
  constructor
  · obtain h3 | h4 := nonneg_or_nonpos_of_mul_nonneg h2
    · addarith [h3]
    · calc
        -k ≤ 0 := by addarith [hk]
        _ ≤ k := hk
        _ ≤ p := by addarith [h4]
  · obtain h5 | h6 := nonneg_or_nonpos_of_mul_nonneg h1
    · addarith [h5]
    · calc
        p ≤ -k := by addarith [h6]
        _ ≤ 0 := by addarith [hk]
        _ ≤ k := hk
