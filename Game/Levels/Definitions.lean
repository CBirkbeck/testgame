import Mathlib


class MyField (F : Type*) extends Add F, Mul F, Zero F, One F where
  add_zero : ∀ a :  F, a + 0 = a
  add_inv : ∀ a : F , ∃ b : F,  a + b = 0 ∧ b + a = 0
  add_comm : ∀ a b :  F , a + b = b + a
  one_mul: ∀ a : F , a * 1 = a
  mul_inv: ∀ a : F , a ≠ 0 → ∃ b : F, a * b = 1 ∧ b * a = 1
  mul_asoc: ∀ a b c : F , (a * b) * c = a * (b * c)
  mul_comm: ∀ a b : F , a * b = b * a
  dist: ∀ a b c : F , (a + b) * c =  (a * c) +  (b * c)

variable {F : Type*} [MyField F]

namespace MyField

lemma test (a b : F) : a + b = b + a := by
  exact add_comm a b

lemma zero_add (a : F) : 0 + a = a := by
  rw [test 0 a]
  apply add_zero
