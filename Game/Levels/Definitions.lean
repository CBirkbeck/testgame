import Mathlib


class MyField (F : Type*) extends Add F, Mul F, Zero F, One F where
  add_zero : ∀ a :  F, a + 0 = a
  add_inv : ∀ a : F , ∃ b : F,  a + b = 0 ∧ b + a = 0
  add_comm : ∀ a b :  F , a + b = b + a
  add_asoc : ∀ a b c : F , (a + b) + c = a + (b +c)
  mul_one: ∀ a : F , a * 1 = a
  mul_inv: ∀ a : F , a ≠ 0 → ∃ b : F, a * b = 1 ∧ b * a = 1
  mul_asoc: ∀ a b c : F, (a * b) * c = a * (b * c)
  mul_comm: ∀ a b : F, a * b = b * a
  dist: ∀ a b c : F, (a + b) * c =  (a * c) +  (b * c)

variable {F : Type*} [MyField F]





class MyVectorSpace (F V : Type*)
  [MyField F] extends Add V, Zero V, SMul F V where
  zero_add : ∀ v : V, 0 + v = v
  add_zero : ∀ v : V, v + 0 = v
  add_inv  : ∀ v : V, ∃ w : V, v + w = 0 ∧ w + v = 0
  add_asoc : ∀ u v w : V, (u + v) + w = u + (v + w)
  add_comm : ∀ u v : V, u + v = v + u
  smul_smul : ∀ (α μ : F) (v : V), α • (μ • v) = (α * μ) • v
  add_smul : ∀ (α μ : F) (v : V), (α + μ) • v = (α • v) + (μ • v)
  smul_add : ∀ (α : F) (v w : V), α • (v + w) = (α • v) + (α • w)
  one_smul : ∀ v : V, (1 : F) • v = v
