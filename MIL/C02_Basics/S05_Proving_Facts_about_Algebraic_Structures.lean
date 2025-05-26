import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  apply le_inf
  . exact inf_le_right
  . exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  have h : ∀ a b c : α, a ⊓ b ⊓ c ≤ a ⊓ (b ⊓ c) := by
    intro a b c
    apply le_inf
    . apply le_trans
      . exact inf_le_left
      . exact inf_le_left
    . apply le_inf
      . apply le_trans
        . exact inf_le_left
        . exact inf_le_right
      . exact inf_le_right
  apply le_antisymm
  . apply h
  . rw [inf_comm x, inf_comm (x ⊓ y), inf_comm x y, inf_comm y z]
    apply h

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    . exact le_sup_right
    . exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  have h : ∀ a b c : α, a ⊔ b ⊔ c ≤ a ⊔ (b ⊔ c) := by
    intro a b c
    apply sup_le
    . apply sup_le
      . exact le_sup_left
      . apply le_trans
        . show b ≤ b ⊔ c
          exact le_sup_left
        . show b ⊔ c ≤ a ⊔ (b ⊔ c)
          exact le_sup_right
    . apply le_trans
      . show c ≤ b ⊔ c
        exact le_sup_right
      . show b ⊔ c ≤ a ⊔ (b ⊔ c)
        exact le_sup_right
  apply le_antisymm
  . apply h
  . rw [sup_comm x, sup_comm (x ⊔ y), sup_comm x y, sup_comm y z]
    apply h

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . exact inf_le_left
  . apply le_inf
    . exact le_rfl
    . exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . apply sup_le
    . exact le_rfl
    . exact inf_le_left
  . exact le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b), absorb1, inf_comm (a ⊔ b), h, ← sup_assoc, inf_comm c, inf_comm c, absorb2]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm (a ⊓ b), absorb2, sup_comm (a ⊓ b), h, ← inf_assoc, sup_comm c, sup_comm c, absorb1]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a]
  apply sub_le_sub_right
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← sub_add_cancel b a]
  nth_rw 1 [← zero_add a]
  apply add_le_add_right
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ : 0 ≤ b - a := by
    rw [← sub_self a]
    apply sub_le_sub_right
    exact h
  rw [← zero_add (a * c), ← sub_add_cancel (b * c) (a * c)]
  apply add_le_add_right
  rw [← mul_sub_right_distrib]
  apply mul_nonneg
  . exact h₁
  . exact h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  apply nonneg_of_mul_nonneg_left
  . show 0 ≤ dist x y * 2
    rw [← dist_self x]
    calc
      dist x x ≤ dist x y + dist y x := dist_triangle x y x
      _ = dist x y + dist x y := by rw [dist_comm y x]
      _ = dist x y * 2 := by ring
  . norm_num

end
