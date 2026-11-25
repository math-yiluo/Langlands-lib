/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.RingTheory.PseudoCoherentApproximationTriangle
import WeilConjectures.RingTheory.MPseudoCoherentShift
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Pseudo-coherence in distinguished triangles

Source: Stacks Project, `more-algebra.tex`, Tag 064R,
`more-algebra-lemma-cone-pseudo-coherent`
(blueprint: lem-pc-ring-pseudo-coherent-distinguished-triangle).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory (IsMPseudoCoherent)

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyLadder
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {S T : Triangle (DerivedCategory (ModuleCat.{v} R))} (φ : S ⟶ T) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceComposableArrows₅
      S i (i + 1) rfl).δlast ⟶
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceComposableArrows₅
      T i (i + 1) rfl).δlast :=
  ComposableArrows.homMk₄ ((DerivedCategory.homologyFunctor _ i).map φ.hom₁)
    ((DerivedCategory.homologyFunctor _ i).map φ.hom₂)
    ((DerivedCategory.homologyFunctor _ i).map φ.hom₃)
    ((DerivedCategory.homologyFunctor _ (i + 1)).map φ.hom₁)
    ((DerivedCategory.homologyFunctor _ (i + 1)).map φ.hom₂)
    (by
      dsimp [-Fin.reduceFinMk]
      simpa only [ComposableArrows.Precomp.map, DerivedCategory.shift_homologyFunctor,
        Functor.map_comp] using (congrArg
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map) φ.comm₁))
    (by
      dsimp [-Fin.reduceFinMk]
      simpa only [ComposableArrows.Precomp.map, DerivedCategory.shift_homologyFunctor,
        Functor.map_comp] using (congrArg
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map) φ.comm₂))
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceδ_naturality
      φ i (i + 1) rfl).symm)
    (by
      dsimp [-Fin.reduceFinMk]
      simpa only [ComposableArrows.Precomp.map, DerivedCategory.shift_homologyFunctor,
        Functor.map_comp] using (congrArg
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map) φ.comm₁))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem approximation_third_map
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) {S T : Triangle (DerivedCategory (ModuleCat.{v} R))}
    (hS : S ∈ distTriang _) (hT : T ∈ distTriang _) (φ : S ⟶ T)
    (h₁ : ∀ i : ℤ, m + 1 < i → IsIso ((DerivedCategory.homologyFunctor _ i).map φ.hom₁))
    (e₁ : Epi ((DerivedCategory.homologyFunctor _ (m + 1)).map φ.hom₁))
    (h₂ : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map φ.hom₂))
    (e₂ : Epi ((DerivedCategory.homologyFunctor _ m).map φ.hom₂)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map φ.hom₃)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map φ.hom₃) := by
  have exactS := fun i =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceComposableArrows₅_exact
      S hS i (i + 1) rfl).δlast
  have exactT := fun i =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceComposableArrows₅_exact
      T hT i (i + 1) rfl).δlast
  constructor
  · intro i hi
    have : Epi ((DerivedCategory.homologyFunctor _ i).map φ.hom₁) := by
      by_cases h : i = m + 1
      · subst i; exact e₁
      · have := h₁ i (by omega)
        infer_instance
    have := h₂ i hi
    have := h₁ (i + 1) (by omega)
    have := h₂ (i + 1) (by omega)
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (exactS i) (exactT i) (homologyLadder φ i)
      (by dsimp [homologyLadder]; infer_instance)
      (by dsimp [homologyLadder]; infer_instance)
      (by dsimp [homologyLadder]; infer_instance)
      (by dsimp [homologyLadder]; infer_instance)
  · have := h₂ (m + 1) (by omega)
    exact Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δ₀Functor.map (homologyLadder φ m)))
      (exactS m).δ₀
      (exactT m).δ₀
      (by dsimp [homologyLadder]; exact e₂)
      (by dsimp [homologyLadder]; exact e₁)
      (by
        dsimp [homologyLadder, -Fin.reduceFinMk]
        infer_instance)

private theorem pseudoCoherent_third
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang _) (hA : IsMPseudoCoherent (m + 1) T.obj₁)
    (hB : IsMPseudoCoherent m T.obj₂) : IsMPseudoCoherent m T.obj₃ := by
  obtain ⟨E, a, b, hGE, hLE, hfree, S, φ, hS, hE, h₁, e₁, h₂, e₂⟩ :=
    DerivedCategory.exists_pseudoCoherent_approximation_triangle R m T hT hA hB
  obtain ⟨hiso, hepi⟩ := approximation_third_map m hS hT φ h₁ e₁ h₂ e₂
  refine ⟨E, a, b, hGE, hLE, hfree, eqToHom hE.symm ≫ φ.hom₃, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    simp only [Functor.map_comp]
    infer_instance
  · have := hepi
    simp only [Functor.map_comp]
    infer_instance

/-- The three two-out-of-three assertions for `m`-pseudo-coherence
(the landed `DerivedCategory.IsMPseudoCoherent` of node def-pc-ring-m-pseudo-coherent).

Source: Stacks Project, `more-algebra.tex`, Tag 064R,
`lemma-cone-pseudo-coherent` (blueprint: lem-pc-ring-pseudo-coherent-distinguished-triangle).

Proof, first clause: choose bounded finite-free witnesses `P ⟶ A` at `m + 1`
and `E ⟶ B` at `m`. Brutally truncate `P` below `m + 1`; the witness conditions
are unchanged. Apply `lem-pc-ring-derived-map-lift` (Stacks Tag 064E) at `n = m`
to lift `P ⟶ A ⟶ B` through `E ⟶ B` to a chain map `γ : P ⟶ E`.
The cone `Q` of `γ` is bounded finite free. The commuting square extends by TR3
(`def-weil-triangulated-category`) to a morphism from the cone triangle to `T`.
Use the long exact cohomology sequences (`lem-sf-derived-homology-long-exact`)
and their commutative ladder (`lem-weil-pbc-derived-cohomology-ladder`).
For `i > m`, in the five terms `Hⁱ(P), Hⁱ(E), Hⁱ(Q), Hⁱ⁺¹(P), Hⁱ⁺¹(E)`,
the first vertical map is surjective and the second, fourth and fifth are
isomorphisms; `lem-weil-pbc-five-lemma` makes the third an isomorphism.
At `i = m`, the four terms `Hᵐ(E), Hᵐ(Q), Hᵐ⁺¹(P), Hᵐ⁺¹(E)` have surjective
first and third vertical maps and an injective fourth map. Apply
`lem-pc-four-lemma-epi` to obtain surjectivity on `Hᵐ(Q) ⟶ Hᵐ(C)`.
Thus `Q ⟶ C` is the required witness.

For the second clause rotate twice to `C ⟶ A[1] ⟶ B[1] ⟶ C[1]` and apply
the first clause at `m - 1`. Since `Hⁱ(A[1]) = Hⁱ⁺¹(A)`, shifting back gives
`m`-pseudo-coherence of `B`. For the third clause rotate once to
`B ⟶ C ⟶ A[1] ⟶ B[1]`, apply the first clause at `m`, and shift back.
Rotation preserves distinguished triangles by `def-weil-abstract-derived-category`. -/
theorem isMPseudoCoherent_of_distinguished_triangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) :
    (IsMPseudoCoherent (m + 1) T.obj₁ →
        IsMPseudoCoherent m T.obj₂ → IsMPseudoCoherent m T.obj₃) ∧
      (IsMPseudoCoherent m T.obj₁ →
        IsMPseudoCoherent m T.obj₃ → IsMPseudoCoherent m T.obj₂) ∧
      (IsMPseudoCoherent (m + 1) T.obj₂ →
        IsMPseudoCoherent m T.obj₃ → IsMPseudoCoherent (m + 1) T.obj₁) := by
  refine ⟨pseudoCoherent_third R m T hT, ?_, ?_⟩
  · intro hA hC
    have hA' : IsMPseudoCoherent (m - 1) T.rotate.rotate.obj₂ :=
      (DerivedCategory.isMPseudoCoherent_shift_one_iff R (m - 1) T.obj₁).mpr (by simpa using hA)
    have hC' : IsMPseudoCoherent (m - 1 + 1) T.rotate.rotate.obj₁ := by
      simpa using hC
    have hB' := pseudoCoherent_third R (m - 1) T.rotate.rotate
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) hC' hA'
    simpa using (DerivedCategory.isMPseudoCoherent_shift_one_iff R (m - 1) T.obj₂).mp hB'
  · intro hB hC
    have hA' := pseudoCoherent_third R m T.rotate (rot_of_distTriang _ hT) hB hC
    exact (DerivedCategory.isMPseudoCoherent_shift_one_iff R m T.obj₁).mp hA'

end CategoryTheory
