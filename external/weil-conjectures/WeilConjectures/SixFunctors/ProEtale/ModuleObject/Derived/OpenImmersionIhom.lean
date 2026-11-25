/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!

# The derived pullback along an open immersion commutes with internal homs

Let `Λ` be a commutative condensed ring and `j : U ⟶ X` an open immersion. This file shows that
the derived pullback `Lj^*` on derived categories of module objects over `Λ` commutes with the
derived internal hom: the comparison `Lj^* RHom(M, N) ⟶ RHom(Lj^* M, Lj^* N)` of the monoidal
functor `Lj^*` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an isomorphism. This is
the first step of the restriction of Verdier biduality to an open subscheme.

## Main results

- `ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion`:
  `Lj^* RHom(M, -) ≅ RHom(Lj^* M, Lj^* -)` via the canonical comparison, on `D(Mod_{Λ_X})`.
- `ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`:
  the same on bounded constructible complexes `Dᵇc(X)⟦Λ⟧`.

## The argument

By `CategoryTheory.Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap` it suffices
that the projection map `Dj_! (Lj^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dj_! T` of the left adjoint `Dj_!` of `Lj^*`
is an isomorphism. Its components are `Dj_!` of an isomorphism (the unit of `Dj_! ⊣ Lj^*` and
the tensorator of `Lj^*` are isomorphisms) followed by the counit at `M ⊗ᴸ Dj_! T`, which is an
isomorphism since `M ⊗ᴸ Dj_! T ≅ Dj_! T ⊗ᴸ M` lies in the essential image of the fully faithful
`Dj_!`
(`ProEtale.CondensedRing.tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

-- the instance search goes through the instances on `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The counit of the adjunction `Dj_! ⊣ Lj^*` along an open immersion `j` is an isomorphism at
`M ⊗ᴸ Dj_! T`, which lies in the essential image of `Dj_!`. -/
lemma isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_counit_app_tensorObj
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).counit.app
      (M ⊗ D((j)_!open⟦Λ⟧).obj T)) := by
  set adj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j
  have hε (Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) : IsIso (adj.counit.app (D((j)_!open⟦Λ⟧).obj Z)) := by
    have : IsIso (D((j)_!open⟦Λ⟧).map (adj.unit.app Z) ≫
        adj.counit.app (D((j)_!open⟦Λ⟧).obj Z)) := by
      rw [adj.left_triangle_components Z]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (D((j)_!open⟦Λ⟧).map (adj.unit.app Z)) _
  obtain ⟨Z, ⟨e⟩⟩ := tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ j T M
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let e' : M ⊗ D((j)_!open⟦Λ⟧).obj T ≅ D((j)_!open⟦Λ⟧).obj Z := (β_ _ _) ≪≫ e.symm
  have h := adj.counit.naturality e'.hom
  dsimp at h
  have : IsIso (adj.counit.app (M ⊗ D((j)_!open⟦Λ⟧).obj T) ≫ e'.hom) := by
    rw [← h]
    have := hε Z
    infer_instance
  exact IsIso.of_isIso_comp_right _ e'.hom

-- the instance search goes through the instances on `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The projection map `Dj_! (Lj^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dj_! T` of the adjunction `Dj_! ⊣ Lj^*` along
an open immersion `j` is an isomorphism. -/
instance isIso_projectionMap_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (Functor.Monoidal.projectionMap
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j) M) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun T ↦ ?_
  have := isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_counit_app_tensorObj
    Λ j M T
  dsimp only [Functor.Monoidal.projectionMap]
  infer_instance

/-- **The derived pullback along an open immersion commutes with internal homs**: for an open
immersion `j : U ⟶ X`, the comparison `Lj^* RHom(M, N) ⟶ RHom(Lj^* M, Lj^* N)` of the monoidal
functor `Lj^*` is an isomorphism. -/
theorem isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (Functor.LaxMonoidal.ihomComparison L((j)^*⟦Λ⟧) M) :=
  Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j) M

/-! ### Bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {V Y : Over (Spec (.of k))}
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (i : V ⟶ Y) [IsOpenImmersion i.left]

-- the instance search goes through the instances on `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The projection map `j_! (Lj^* M ⊗ᴸ T) ⟶ M ⊗ᴸ j_! T` of the adjunction `j_! ⊣ Lj^*` along an
open immersion `j` on bounded constructible complexes is an isomorphism. -/
instance isIso_projectionMap_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Functor.Monoidal.projectionMap
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj
          ℓ) ℓ i) M) := by
  set adj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ i
  have hη (T : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (adj.unit.app T) := by
    have : IsIso ((boundedConstructible _).ι.map (adj.unit.app T)) := by
      simp only [adj, boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction,
        Adjunction.map_restrictFullyFaithful_unit_app]
      have := NatIso.isIso_app_of_isIso
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' (Profinite.padicAlgClRingObj
            ℓ) i.left).unit
        ((boundedConstructible _).ι.obj T)
      exact IsIso.comp_isIso' this inferInstance
    exact isIso_of_reflects_iso _ (boundedConstructible _).ι
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun T ↦ ?_
  have hε : IsIso (adj.counit.app (M ⊗ (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
      T)) := by
    have : IsIso ((boundedConstructible _).ι.map (adj.counit.app
        (M ⊗ (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            T))) := by
      simp only [adj, boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction,
        Adjunction.map_restrictFullyFaithful_counit_app]
      have :=
        isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_counit_app_tensorObj
          (Profinite.padicAlgClRingObj ℓ) i.left M.obj T.obj
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)
    exact isIso_of_reflects_iso _ (boundedConstructible _).ι
  have := hη T
  dsimp only [Functor.Monoidal.projectionMap]
  infer_instance

/-- **The pullback along an open immersion commutes with internal homs on bounded constructible
complexes**: for an open immersion `j : U ⟶ X`, the comparison
`Lj^* RHom(M, N) ⟶ RHom(Lj^* M, Lj^* N)` of the monoidal functor `Lj^* : Dᵇc(X) ⥤ Dᵇc(U)` is an
isomorphism. -/
theorem isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Functor.LaxMonoidal.ihomComparison (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ i) M) :=
  Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        ℓ i) M

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
