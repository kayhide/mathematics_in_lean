import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  inv_mem : a ∈ carrier → a⁻¹ ∈ carrier

instance [Group G] : SetLike (Subgroup₁ G) G where
  coe x := x.carrier
  coe_injective' _ _ := Subgroup₁.ext

instance [Group G] (H : Subgroup₁ G): Group H where
  mul := fun ⟨x, xh⟩ ⟨y, yh⟩ ↦ ⟨x * y, H.mul_mem xh yh⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, H.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
  inv := fun ⟨x, xh⟩ ↦ ⟨x⁻¹, H.inv_mem xh⟩
  inv_mul_cancel := fun ⟨x, _⟩ ↦ SetCoe.ext (inv_mul_cancel x)



instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z
      rintro ⟨a, ha, b, hb, h₁⟩
      rintro ⟨c, hc, d, hd, h₂⟩
      use (a * c), mul_mem ha hc
      use (d * b), mul_mem hd hb
      rw [← mul_assoc x, h₁]
      rw [← mul_assoc z, ← h₂]
      rw [mul_assoc, mul_comm b c, mul_assoc]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
      rintro a b ⟨x, hx, y, hy, h₁⟩ c d ⟨z, hz, w, hw, h₂⟩
      simp
      use (x * z), mul_mem hx hz
      use (y * w), mul_mem hy hw
      calc
        (a * c) * (x * z) = a * (c * x) * z := by repeat rw [mul_assoc]
        _ = a * (x * c) * z := by rw [mul_comm c x]
        _ = (a * x) * (c * z) := by repeat rw [mul_assoc]
        _ = (b * y) * (d * w) := by rw [h₁, h₂]
        _ = b * (y * d) * w := by repeat rw [mul_assoc]
        _ = b * (d * y) * w := by rw [mul_comm y d]
        _ = b * d * (y * w) := by repeat rw [mul_assoc]
        )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound
      simp
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      simp
  mul_one := by
      rintro ⟨_⟩
      apply Quotient.sound
      simp
