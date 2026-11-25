/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.TateTwist.RootsOfUnityUpperStar

/-!
# Semilinear pullback of root generators

The generator of the roots-of-unity sheaf attached to a root in a field transforms
under a semilinear scheme morphism by applying the corresponding field homomorphism.
This is the finite-level equation needed to compare the roots-defined Tate line
with its cyclotomic scalar description.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)
  {U : Scheme.{u}} (f : U ⟶ Spec (.of L))

/-- Changing the base field map changes the map into sections by composition. -/
lemma fieldToSections_comp_Spec_map (V : U.ProEt) :
    fieldToSections (f ≫ Spec.map (CommRingCat.ofHom φ)) V =
      CommRingCat.ofHom φ ≫ fieldToSections f V := by
  unfold fieldToSections
  rw [← Category.assoc, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- A field homomorphism carries the generator associated to `z` to the generator
associated to its image. -/
lemma unitToRootsOfUnity_comp_map {N : ℕ} (z : rootsOfUnity N K) :
    unitToRootsOfUnity z ≫
        (CommRingCat.rootsOfUnityFunctor N).map (CommRingCat.ofHom φ) =
      unitToRootsOfUnity (restrictRootsOfUnity φ N z) := by
  ext a
  apply ULift.ext
  exact map_zsmul (restrictRootsOfUnity φ N).toAdditive a.down (Additive.ofMul z)

/-- The presheaf generator is compatible with a change in the base field map. -/
lemma unitToRootsOfUnityPresheaf_comp_Spec_map {N : ℕ} (z : rootsOfUnity N K) :
    unitToRootsOfUnityPresheaf (f ≫ Spec.map (CommRingCat.ofHom φ)) z =
      unitToRootsOfUnityPresheaf f (restrictRootsOfUnity φ N z) := by
  ext V : 2
  dsimp only [unitToRootsOfUnityPresheaf]
  rw [fieldToSections_comp_Spec_map, Functor.map_comp, ← Category.assoc,
    unitToRootsOfUnity_comp_map]

/-- The sheaf generator is compatible with a change in the base field map. -/
lemma unitToRootsOfUnitySheaf_comp_Spec_map {N : ℕ} [NeZero N] {ζ : K}
    (hζ : ζ ^ N = 1) (hφζ : φ ζ ^ N = 1) :
    unitToRootsOfUnitySheaf (f ≫ Spec.map (CommRingCat.ofHom φ)) hζ =
      unitToRootsOfUnitySheaf f hφζ := by
  rw [unitToRootsOfUnitySheaf_eq, unitToRootsOfUnitySheaf_eq,
    unitToRootsOfUnityPresheaf_comp_Spec_map]
  congr 2
  ext
  rfl

/-- Pullback along a semilinear scheme morphism sends the generator `ζ` to `φ ζ`. -/
lemma upperStar_map_unitToRootsOfUnitySheaf_semilinear
    {X : Scheme.{u}} (g : U ⟶ X) (s : X ⟶ Spec (.of K))
    (hg : g ≫ s = f ≫ Spec.map (CommRingCat.ofHom φ)) {N : ℕ} [NeZero N]
    {ζ : K} (hζ : ζ ^ N = 1) (hφζ : φ ζ ^ N = 1) :
    (g)^*[Ab.{u + 1}].map
        (unitToRootsOfUnitySheaf s hζ ≫ (rootsOfUnitySheafIso X N).hom) ≫
          upperStarRootsOfUnityComparison g N =
      Functor.OplaxMonoidal.η (g)^*[Ab.{u + 1}] ≫
        unitToRootsOfUnitySheaf f hφζ ≫ (rootsOfUnitySheafIso U N).hom := by
  rw [upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison g s
    (f ≫ Spec.map (CommRingCat.ofHom φ)) hg hζ,
    unitToRootsOfUnitySheaf_comp_Spec_map φ f hζ hφζ]

end AlgebraicGeometry.ProEtale
