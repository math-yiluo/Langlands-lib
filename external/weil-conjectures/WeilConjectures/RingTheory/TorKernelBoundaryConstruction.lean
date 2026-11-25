/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Constructing the kernel boundary from a projective resolution

Source: Stacks Project, Algebra, Tags 00LZ and 00M0.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace CategoryTheory

/-- The tensor complex used to compute first-variable Tor. -/
noncomputable abbrev torKernelComplex {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) :=
  (((MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (projectiveResolution N).complex

/-- Lift the augmentation through the presentation. The lift need not be unique;
the induced map on homology will be independent of it. -/
noncomputable def torKernelLift {R : Type u} [CommRing R]
    {F N : ModuleCat.{u} R} (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (projectiveResolution N).complex.X 0 ⟶ F := by
  have : Epi (ModuleCat.ofHom q) := (ModuleCat.epi_iff_surjective _).mpr hq
  exact Projective.factorThru ((projectiveResolution N).π.f 0) (ModuleCat.ofHom q)

@[reassoc (attr := simp)]
theorem torKernelLift_comp {R : Type u} [CommRing R]
    {F N : ModuleCat.{u} R} (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    torKernelLift q hq ≫ ModuleCat.ofHom q = (projectiveResolution N).π.f 0 := by
  have : Epi (ModuleCat.ofHom q) := (ModuleCat.epi_iff_surjective _).mpr hq
  exact Projective.factorThru_comp _ _

/-- The lifted differential, with codomain restricted to the kernel. -/
noncomputable def torKernelDifferential {R : Type u} [CommRing R]
    {F N : ModuleCat.{u} R} (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (projectiveResolution N).complex.X 1 →ₗ[R] LinearMap.ker q :=
  (((projectiveResolution N).complex.d 1 0 ≫ torKernelLift q hq).hom).codRestrict
    (LinearMap.ker q) (by
      intro x
      change (((projectiveResolution N).complex.d 1 0 ≫ torKernelLift q hq) ≫
        ModuleCat.ofHom q).hom x = 0
      rw [Category.assoc, torKernelLift_comp,
        (projectiveResolution N).complex_d_comp_π_f_zero]
      rfl)

/-- The lifted differential kills degree-two boundaries, already before tensoring. -/
theorem torKernelDifferential_boundary {R : Type u} [CommRing R]
    {F N : ModuleCat.{u} R} (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (projectiveResolution N).complex.d 2 1 ≫
      ModuleCat.ofHom (torKernelDifferential q hq) = 0 := by
  ext x
  change (((projectiveResolution N).complex.d 2 1 ≫
    (projectiveResolution N).complex.d 1 0) ≫ torKernelLift q hq).hom x = 0
  rw [HomologicalComplex.d_comp_d, zero_comp]
  rfl

/-- The tensor of the lifted differential kills boundaries. -/
theorem torKernelTensor_boundary {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {F N : ModuleCat.{u} R}
    (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (torKernelComplex M N).d 2 1 ≫
      ModuleCat.ofHom ((torKernelDifferential q hq).rTensor M) = 0 := by
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  change T.map ((projectiveResolution N).complex.d 2 1) ≫
    T.map (ModuleCat.ofHom (torKernelDifferential q hq)) = 0
  rw [← T.map_comp, torKernelDifferential_boundary, T.map_zero]

/-- The actual boundary on first homology, defined by the cokernel universal property. -/
noncomputable def torKernelHomologyBoundary {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {F N : ModuleCat.{u} R}
    (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (torKernelComplex M N).homology 1 ⟶ ModuleCat.of R (LinearMap.ker q ⊗[R] M) :=
  ((torKernelComplex M N).homologyIsCokernel 2 1
    ((ComplexShape.down ℕ).prev_eq' (by simp))).desc (CokernelCofork.ofπ
    ((torKernelComplex M N).iCycles 1 ≫
      ModuleCat.ofHom ((torKernelDifferential q hq).rTensor M)) (by
      rw [← Category.assoc, HomologicalComplex.toCycles_i]
      exact torKernelTensor_boundary M q hq))

/-- Canonical connecting map, using the resolution identification of Tor and the
cycle formula for the lifted augmentation. All data above are constructed; no
existential exactness theorem is used to choose a boundary.
(blueprint: def-sc-p1-tor-kernel-boundary-construction) -/
noncomputable def torKernelBoundary {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (F N : ModuleCat.{u} R)
    (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
      (LinearMap.ker q ⊗[R] M) :=
  (((projectiveResolution N).isoLeftDerivedObj
    ((MonoidalCategory.tensoringRight (ModuleCat R)).obj M) 1).hom ≫
      torKernelHomologyBoundary M q hq).hom

end CategoryTheory
