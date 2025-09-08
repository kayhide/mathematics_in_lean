import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap End

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x
  rw [Submodule.mem_inf]
  repeat rw [LinearMap.mem_ker]
  intro hx
  rcases h with ⟨U, V, hUV⟩
  have : aeval φ (1 : K[X]) x = aeval φ (U * P + V * Q) x := by rw [hUV]
  simp at this
  simpa [hx]

#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  apply le_antisymm
  . apply sup_le
    . rw [mul_comm, map_mul]
      apply LinearMap.ker_le_ker_comp
    . rw [map_mul]
      apply LinearMap.ker_le_ker_comp
  . intro x hx
    rcases h with ⟨U, V, hUV⟩
    have : x = (aeval φ (U * P) + aeval φ (V * Q)) x := by
      calc
        x = aeval φ (1 : K[X]) x := by simp
        _ = aeval φ (U * P + V * Q) x := by simp [hUV]
        _ = (aeval φ (U * P) + aeval φ (V * Q)) x := by simp
    rw [this, add_comm]
    rw [mem_ker] at hx
    apply Submodule.add_mem_sup
    . rw [mem_ker]
      rw [← mul_apply, ← map_mul]
      have : P * (V * Q) = V * (P * Q) := by ring
      rw [this]
      rw [map_mul, mul_apply, hx]
      simp
    . rw [mem_ker]
      rw [← mul_apply, ← map_mul]
      have : Q * (U * P) = U * (P * Q) := by ring
      rw [this]
      rw [map_mul, mul_apply, hx]
      simp

example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def



example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
