/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.FormallySmoothAdicUniverseLift
public import WeilConjectures.RingTheory.FormallySmoothAdic

/-!
# Base change of formal smoothness for an adic topology

Source: Stacks Project, More on Algebra, Lemma 07EG (blueprint: lem-weil-pbc-fs-adic-base-change).
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Formal smoothness for an adic topology is preserved by arbitrary base change.
Source: Stacks Project, More on Algebra, Lemma 07EG
(blueprint: lem-weil-pbc-fs-adic-base-change).

Proof:
1. For a square-zero ideal `J` of a commutative `R'`-algebra `D` and an `R'`-algebra
   map `g' : S ⊗[R] R' → D/J` killing the `k`-th power of the extended ideal,
   restrict along `includeLeft` to an `R`-algebra map `g : S → D/J`. Regard `D`
   as an `R`-algebra through `R → R' → D`
   (`def-weil-pbc-algebra-hom-quotient`,
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`).
2. The inclusion carries `n ^ k` into the `k`-th power of the extended ideal,
   since it carries every product of `k` elements of `n` there. Thus `g` kills
   `n ^ k` and is continuous (`def-weil-pbc-algebra-hom-quotient`).
3. Apply `h` to obtain an `R`-algebra lift `f : S → D` of `g`
   (`theorem-finite-etale-covers-proper-henselian--2`).
4. The tensor-product pushout property extends `f` and the structure map `R' → D`
   to `f' : S ⊗[R] R' → D`, sending `s ⊗ r'` to `f(s) * r'`. Its restriction
   to `R'` is the structure map, so it is an `R'`-algebra map
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`).
5. The quotient of `f'` and `g'` agree after both tensor-factor inclusions;
   pushout uniqueness makes them equal. This solves every lifting problem
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`,
   `def-weil-pbc-algebra-hom-quotient`, `theorem-finite-etale-covers-proper-henselian--2`). -/
theorem formallySmoothAdic_tensorProduct
    (R : Type u) (S : Type v) (R' : Type w)
    [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (n : Ideal S)
    (h : FormallySmoothAdic R S n) :
    letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    FormallySmoothAdic R' (S ⊗[R] R')
      (n.map (algebraMap S (S ⊗[R] R'))) := by
  let : Algebra R (S ⊗[R] R') := Algebra.TensorProduct.leftAlgebra
  let : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  intro D _ _ J hJ g' hg'
  let : Algebra R D :=
    ((algebraMap R' D).comp (algebraMap R R')).toAlgebra
  let : IsScalarTower R R' D := IsScalarTower.of_algebraMap_eq' (by rfl)
  let : Algebra R (D ⧸ J) :=
    ((algebraMap R' (D ⧸ J)).comp (algebraMap R R')).toAlgebra
  let : IsScalarTower R R' (D ⧸ J) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      change _ = Ideal.Quotient.mk J ((algebraMap R' D) (algebraMap R R' r))
      rfl)
  rcases hg' with ⟨k, hk, hgk⟩
  let ι : S →ₐ[R] S ⊗[R] R' := Algebra.TensorProduct.includeLeft
  let g : S →ₐ[R] D ⧸ J := (g'.restrictScalars R).comp ι
  have hgn : ∀ x ∈ n ^ k, g x = 0 := by
    intro x hx
    change g' (ι x) = 0
    apply hgk
    have hx' : ι x ∈ (n.map ι.toRingHom) ^ k := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem ι.toRingHom hx
    exact hx'
  obtain ⟨f, hf⟩ := formallySmoothAdic_lift_universe R S n h D J hJ g
    ⟨k, hk, hgn⟩
  let ρ : R' →ₐ[R] D := (Algebra.ofId R' D).restrictScalars R
  let f'R : (S ⊗[R] R') →ₐ[R] D := Algebra.TensorProduct.productMap f ρ
  let f' : (S ⊗[R] R') →ₐ[R'] D :=
    { toRingHom := f'R.toRingHom
      commutes' := by
        intro r'
        change f'R (algebraMap R' (S ⊗[R] R') r') = algebraMap R' D r'
        rw [show algebraMap R' (S ⊗[R] R') r' =
          Algebra.TensorProduct.includeRight r' by rfl]
        simp [f'R, ρ] }
  let q : D →ₐ[R'] D ⧸ J := Ideal.Quotient.mkₐ R' J
  have hleft : ((q.comp f').restrictScalars R).comp ι =
      (g'.restrictScalars R).comp ι := by
    ext x
    change q (f'R (ι x)) = g x
    simpa [f'R, q, ι, f'] using congrArg (fun z => z x) hf
  have hright :
      ((q.comp f').restrictScalars R).comp Algebra.TensorProduct.includeRight =
        (g'.restrictScalars R).comp Algebra.TensorProduct.includeRight := by
    ext x
    change q (f'R (Algebra.TensorProduct.includeRight x)) =
      g' (Algebra.TensorProduct.includeRight x)
    rw [show f'R (Algebra.TensorProduct.includeRight x) = algebraMap R' D x by
      simp [f'R, ρ]]
    rw [q.commutes, ← g'.commutes x]
    rfl
  have heq : (q.comp f').restrictScalars R = g'.restrictScalars R :=
    Algebra.TensorProduct.ext hleft hright
  refine ⟨f', ?_⟩
  exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun heq x)

end Algebra
