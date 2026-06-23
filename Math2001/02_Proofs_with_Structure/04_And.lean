/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  . apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, h2⟩ := hp'
  calc
    p >= -3 := by rel[h1]
    _ >= -5 := by numbers


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a * a = 0
  · apply le_antisymm
    calc
      a * a = a ^ 2 := by ring
      _ ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    calc
      a * a = a ^ 2 := by ring
      _ >= 0 := by extra
  have h3 : b * b = 0
  . apply le_antisymm
    calc
      b * b = b ^ 2 := by ring
      _ <= a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw[h1]
    calc
      b * b = b ^ 2 := by ring
      _ >= 0 := by extra
  constructor
  have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain h4a | h4b := h4
  . exact h4a
  . exact h4b
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  obtain h5a | h5b := h5
  . exact h5a
  . exact h5b

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1,h2⟩ := H
  calc
    2 * a + b = (a) + (a + b) := by ring
    _ <= 1 + (a + b) := by rel [h1]
    _ <= 1 + 3 := by rel[h2]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
    _ <= 1 + (r-s) := by rel[h1]
    _ <= 1 + 5 := by rel[h2]
    _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m = (m + 5) - 5 := by ring
    _ <= n - 5 := by rel[h2]
    _ <= 8 - 5 := by rel[h1]
    _ = 3 := by numbers

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p >= 7 := by addarith[hp]
  constructor
  . calc
      p ^ 2 >= 7 ^ 2 := by rel[hp']
      _ = 49 := by numbers
  . apply hp'

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h' : a >= 6 := by addarith[h]
  constructor
  . apply h'
  . calc
      3 * a >= 3 * 6 := by rel[h']
      _ = 10 + 8 := by numbers
      _ >= 10 := by extra


example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : y = 2 :=
    calc
      y = 2 * y - y := by ring
      _ = (7 - x) - y := by addarith[h2]
      _ = (7 - x) - (5 - x) := by addarith[h1]
      _ = 2 := by ring
  constructor
  . calc
      x = 5 - y := by addarith[h1]
      _ = 5 - 2 := by rw[h3]
      _ = 3 := by numbers
  . apply h3


example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : a * (b - 1) = 0 :=
    calc
      a * (b-1) = a*b - a := by ring
      _ = a - a := by rw[h1]
      _ = 0 := by ring
  have h4 : b * (a - 1) = 0 :=
    calc
      b * (a-1) = b*a - b := by ring
      _ = a*b - b := by ring
      _ = b - b := by rw[h2]
      _ = 0 := by ring
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  have h6 := eq_zero_or_eq_zero_of_mul_eq_zero h4
