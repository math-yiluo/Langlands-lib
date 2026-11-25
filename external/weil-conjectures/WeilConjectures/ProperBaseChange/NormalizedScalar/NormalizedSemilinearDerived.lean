/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationLift

/-! # Scalar endomorphisms under an exact derived functor -/

@[expose] public section
set_option autoImplicit false
universe uA uB vA vB wA wB wR wS
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.NormalizedScalar

/-- Exact derivation preserves a specified semilinear scalar-identity equation.
Source: exact termwise factorization and essential surjectivity of localization.
(blueprint: lem-weil-pbc-normalized-semilinear-derived).

Proof: on a complex the equation holds degree by degree. The exact-factorization
comparison transports it to its image in the derived category. Every derived
object is isomorphic to such an image, and scalar identity morphisms are invariant
under conjugation. Thus the same equation holds on every derived object. -/
theorem mapDerivedCategory_scalar
    {R : Type wR} [CommRing R] {S : Type wS} [CommRing S] (φ : R →+* S)
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A] [Linear R A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [Linear S B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ r X, F.map (r • 𝟙 X) = φ r • 𝟙 (F.obj X))
    (r : R) (K : DerivedCategory A) :
    F.mapDerivedCategory.map (r • 𝟙 K) = φ r • 𝟙 (F.mapDerivedCategory.obj K) := by
  have hP (P : CochainComplex A ℤ) :
      F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj P)) =
        φ r • 𝟙 (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    have h : (F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 P) =
        φ r • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext n
      exact hF r (P.X n)
    have he := F.mapDerivedCategoryFactors.hom.naturality (r • 𝟙 P)
    simp only [CategoryTheory.Functor.comp_map, h, CategoryTheory.Functor.map_smul] at he
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at he
    simp only [Linear.comp_smul] at he
    erw [Category.comp_id] at he
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).1
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.comp_id,
      Category.id_comp] using he
  let e := DerivedCategory.Q.objObjPreimageIso K
  rw [← CategoryTheory.Rationalization.smul_id_conj e r, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, hP]
  simp

end WeilConjectures.NormalizedScalar
