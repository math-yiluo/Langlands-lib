/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
public import Mathlib.RingTheory.Flat.Localization

/-!
# Local pseudo-coherence of a localization cone

Source: Stacks Project, More on Algebra, Tag 066D, local cone step,
and Tag 064R, first distinguished-triangle assertion.
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-local).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private instance scalar_additive
    {A B : Type u₁} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem scalar_exact
    {A B : Type u₁} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁} f) := by
  algebraize [f]
  let F := ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁} f
  have hex : ∀ S : ShortComplex (ModuleCat.{max u₁ v₁} A),
      S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    convert Module.Flat.lTensor_exact B (f := S.f.hom) (g := S.g.hom) hS using 1
    all_goals simp only [F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
      ModuleCat.ExtendScalars.map', ModuleCat.restrictScalars,
      ModuleCat.RestrictScalars.obj', LinearMap.baseChange]
    all_goals rfl
  have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 2 4).mp hex
  exact h.1

private theorem pseudoCoherent_mono
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{max u₁ v₁} A))
    (h : IsMPseudoCoherent m C) : IsMPseudoCoherent (m + 1) C := by
  obtain ⟨E, a, b, hGE, hLE, hfree, f, hiso, hepi⟩ := h
  refine ⟨E, a, b, hGE, hLE, hfree, f, ?_, ?_⟩
  · intro i hi
    exact hiso i (by omega)
  · have := hiso (m + 1) (by omega)
    infer_instance

private theorem pseudoCoherent_of_iso
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (m : ℤ) {C D : DerivedCategory (ModuleCat.{max u₁ v₁} A)} (e : C ≅ D)
    (h : IsMPseudoCoherent m C) : IsMPseudoCoherent m D := by
  obtain ⟨E, a, b, hGE, hLE, hfree, f, hiso, hepi⟩ := h
  refine ⟨E, a, b, hGE, hLE, hfree, f ≫ e.hom, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    simp only [Functor.map_comp]
    infer_instance
  · have := hepi
    simp only [Functor.map_comp]
    infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem pseudoCoherent_scalar
    {A B : Type u₁} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    [HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} B)]
    (f : A →+* B) [PreservesFiniteLimits
      (ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁} f)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{max u₁ v₁} A))
    (h : IsMPseudoCoherent m C) :
    IsMPseudoCoherent m ((ModuleCat.extendScalars f).mapDerivedCategory.obj C) := by
  algebraize [f]
  let F := ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁} f
  obtain ⟨E, a, b, hGE, hLE, hfree, g, hiso, hepi⟩ := h
  have := hGE
  have := hLE
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj E, a, b,
    inferInstance, inferInstance, ?_,
    F.mapDerivedCategoryFactors.inv.app E ≫ F.mapDerivedCategory.map g, ?_, ?_⟩
  · intro i
    have := (hfree i).1
    have := (hfree i).2
    dsimp [F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
      ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
    exact ⟨inferInstance, inferInstance⟩
  · intro i hi
    have := hiso i hi
    have : IsIso (((homologyFunctor (ModuleCat.{max u₁ v₁} A) i) ⋙ F).map g) := by
      dsimp
      infer_instance
    have : IsIso ((homologyFunctor (ModuleCat.{max u₁ v₁} B) i).map
        (F.mapDerivedCategory.map g)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) g).mp this
    simp only [Functor.map_comp]
    infer_instance
  · have := hepi
    have : Epi (((homologyFunctor (ModuleCat.{max u₁ v₁} A) m) ⋙ F).map g) := by
      dsimp
      infer_instance
    have : Epi ((homologyFunctor (ModuleCat.{max u₁ v₁} B) m).map
        (F.mapDerivedCategory.map g)) := by
      change Epi ((F.mapDerivedCategory ⋙
        homologyFunctor (ModuleCat.{max u₁ v₁} B) m).map g)
      rw [← NatIso.naturality_2 (F.mapDerivedCategoryHomologyFunctorIso m).symm g]
      infer_instance
    simp only [Functor.map_comp]
    infer_instance

-- The unused hypotheses belong to the unchanged interface of the cone construction.
set_option linter.unusedVariables false in
/-- Exact localization transports pseudo-coherence across the cone constructed in
`localization_cone_construction` (Stacks, Tag 066D).
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-local).

Proof: an `m`-approximation is also an `(m + 1)`-approximation, since its cohomology map
in degree `m + 1` is an isomorphism. Localization is flat, so extension of scalars is
exact and induces a triangulated functor commuting with cohomology. Apply this functor
to a bounded finite-free witness for `E`; boundedness and finite freeness persist, as do
the cohomology isomorphisms and epimorphism. Thus the first object of the localized
triangle is `(m + 1)`-pseudo-coherent. Its second object is `m`-pseudo-coherent by
`hlocal`, after the canonical comparison with termwise localization. The first clause
of Tag 064R now gives `m`-pseudo-coherence of its third object. The same canonical
comparison identifies that object with the termwise localization of `N`. -/
theorem localization_cone_local
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁}
      (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj M)))
    (E N : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (a : Q.obj E ⟶ Q.obj M) (b : Q.obj M ⟶ Q.obj N)
    (c : Q.obj N ⟶ (Q.obj E)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)))
    (hE : IsMPseudoCoherent m (Q.obj E))
    (hN : ∀ j : ℤ, n - 1 < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj N))) :
    ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj N)) := by
  intro i
  let F := ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁}
    (algebraMap A (Localization.Away (f i)))
  have : PreservesFiniteLimits F := scalar_exact _
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away (f i)) (Submonoid.powers (f i))))
  let T := F.mapDerivedCategory.mapTriangle.obj (Triangle.mk a b c)
  have hT' : T ∈ distTriang _ := F.mapDerivedCategory.map_distinguished _ hT
  have hE' : IsMPseudoCoherent (m + 1) T.obj₁ :=
    pseudoCoherent_scalar _ (m + 1) _ (pseudoCoherent_mono m _ hE)
  have hM' : IsMPseudoCoherent m T.obj₂ :=
    pseudoCoherent_of_iso m (F.mapDerivedCategoryFactors.app M).symm (hlocal i)
  have hN' := (isMPseudoCoherent_of_distinguished_triangle
    (Localization.Away (f i)) m T hT').1 hE' hM'
  exact pseudoCoherent_of_iso m (F.mapDerivedCategoryFactors.app N) hN'

end DerivedCategory
