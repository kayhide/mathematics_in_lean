import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h
    intro x xs
    exact h ⟨x, xs, rfl⟩
  . intro h
    rintro x ⟨y, ys, rfl⟩
    exact h ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fyfx⟩
  rw [← h fyfx]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, fxu, rfl⟩
  exact fxu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y
  rw [Surjective] at h
  rcases h y with ⟨x, rfl⟩
  intro fxu
  use x, fxu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, rfl⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xfu
  use h xfu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  . rintro (fxu | fxv)
    . exact Or.inl fxu
    . exact Or.inr fxv
  . rintro (xfu | xfv)
    . exact Or.inl xfu
    . exact Or.inr xfv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨⟨xs, xt⟩, rfl⟩⟩
  use ⟨x, ⟨xs, rfl⟩⟩, x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨yfs, yft⟩
  rw [Injective] at h
  rcases yfs with ⟨x, xs, rfl⟩
  rcases yft with ⟨x', x't, fx'fx⟩
  rcases h fx'fx with rfl
  use x', ⟨xs, x't⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ynft⟩
  use x
  constructor
  . constructor
    . exact xs
    . intro xt
      apply ynft
      use x
  . rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨xfu, xnfv⟩
  use xfu, xnfv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  . rintro y ⟨yfs, yv⟩
    rcases yfs with ⟨x, xs, rfl⟩
    use x
    constructor
    . exact ⟨xs, yv⟩
    . rfl
  . rintro y ⟨x, ⟨xs, xfv⟩, rfl⟩
    use ⟨x, ⟨xs, rfl⟩⟩, xfv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨⟨xs, xfu⟩, rfl⟩⟩
  use ⟨x, ⟨xs, rfl⟩⟩, xfu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xfu⟩
  constructor
  . use x, xs
  . exact xfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | xfu)
  . left
    use x, xs
  . right
    exact xfu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  . rintro ⟨x, xmem, rfl⟩
    rcases xmem with ⟨xset, ⟨xsetmem, xmem⟩⟩
    rcases xsetmem with ⟨i, rfl⟩
    simp at xmem
    simp
    use i, x, xmem
  . rintro ⟨yset, ysetmem, ymem⟩
    simp at ysetmem
    rcases ysetmem with ⟨i, rfl⟩
    rcases ymem with ⟨x, xmem, rfl⟩
    simp
    use x, ⟨i, xmem⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y ⟨x, xmem, h⟩
  rcases h with rfl
  simp at xmem
  simp
  intro i
  use x, (xmem i)

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y h
  simp at h
  simp
  rcases h i with ⟨x, xmem, rfl⟩
  use x
  constructor
  . intro j
    rcases h j with ⟨x', x'mem, h'⟩
    rcases injf h' with rfl
    exact x'mem
  . rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  . rintro ⟨yset, ysetmem, ymem⟩
    simp at ysetmem
    rcases ysetmem with ⟨i, rfl⟩
    simp
    use i
  . rintro ⟨xset, xsetmem, xmem⟩
    simp at xsetmem
    rcases xsetmem with ⟨i, rfl⟩
    simp
    use i, xmem

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro xmem
    simp at xmem
    simp
    intro i
    exact xmem i
  . intro xmem
    simp at xmem
    simp
    intro i
    exact xmem i

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro h
  calc
    x = √x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = √y ^ 2 := by rw [h]
    _ = y := by rw [sq_sqrt ynonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro h
  simp at h
  calc
    x = √ (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = √ (y ^ 2) := by rw [h]
    _ = y := by rw [sqrt_sq ynonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  . rintro ⟨x, xmem, rfl⟩
    simp at xmem
    simp
  . intro ymem
    simp at ymem
    simp
    use y ^ 2
    exact ⟨pow_two_nonneg y, sqrt_sq ymem⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  . rintro ⟨x, rfl⟩
    simp
    exact pow_two_nonneg x
  . intros ymem
    simp at ymem
    simp
    use √y
    apply sq_sqrt ymem

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf
    rw [LeftInverse]
    intro x
    have h : ∃y, f y = f x := ⟨x, rfl⟩
    rw [inverse, dif_pos h]
    exact injf (Classical.choose_spec h)
  . intro linv
    rw [LeftInverse] at linv
    intro x y h
    rw [← linv x, ← linv y, h]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surjf
    rw [RightInverse, LeftInverse]
    intro y
    rw [Surjective] at surjf
    rcases surjf y with ⟨x, rfl⟩
    have h : ∃z, f z = f x := ⟨x, rfl⟩
    rw [inverse, dif_pos h]
    exact Classical.choose_spec h
  . intro rinv
    rw [RightInverse, LeftInverse] at rinv
    rw [Surjective]
    intro y
    rw [← rinv y]
    use inverse f y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
