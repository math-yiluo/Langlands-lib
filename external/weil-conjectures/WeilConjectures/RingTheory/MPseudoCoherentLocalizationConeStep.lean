/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeConstruction
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeLocal

/-!
# Lowering the cohomology bound in pseudo-coherent localization descent

Source: Stacks Project, Tag 066D, proof, second and third paragraphs.
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A finite-free top-cohomology approximation lowers the bound by one and preserves the
fixed-degree pseudo-coherence of every localization. Only a single induction step is asserted.
Source: Stacks Project, Tag 066D, proof, second and third paragraphs, using Tags 064S,
00EO (2), and 064R.
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-step).

Proof: For `n ≥ m`, a bounded finite-free witness to local `m`-pseudo-coherence also
witnesses local `n`-pseudo-coherence. Exact localization identifies local cohomology with
localized global cohomology, so the upper bound gives local vanishing above `n`.
Tag 064S gives finite generation of local degree-`n` cohomology. Tag 00EO (2) then gives
finite generation of `Hⁿ(M)` over `A`. Choose a finite free module surjecting onto `Hⁿ(M)`.
Its projectivity lifts the map through cycles, giving a chain map from the single-term
complex `E` in degree `n` to `M`. Let `N` be the explicit mapping cone of this chain map,
and take its distinguished triangle after applying `Q`. The long exact sequence and
surjectivity in degree `n` show that `Hʲ(N) = 0` for `j > n - 1`. The bounded finite-free
complex `E` is `k`-pseudo-coherent for every `k` using its identity. Its localization is
also bounded finite free. Localization is exact and commutes with cones, so the first
clause of Tag 064R shows that every localization of `N` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_localization_cone_step
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j →
      IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) :
    ∃ (E N : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
      (a : Q.obj E ⟶ Q.obj M) (b : Q.obj M ⟶ Q.obj N)
      (c : Q.obj N ⟶ (Q.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)) ∧
      IsMPseudoCoherent m (Q.obj E) ∧
      (∀ j : ℤ, n - 1 < j →
        IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj N))) ∧
      (∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj N))) := by
  obtain ⟨E, N, a, b, c, hT, hE, hN⟩ :=
    localization_cone_construction M r f hf m n hmn hvan hlocal
  refine ⟨E, N, a, b, c, hT, hE, hN, ?_⟩
  exact localization_cone_local M r f hf m n hmn hvan hlocal E N a b c hT hE hN

end DerivedCategory
