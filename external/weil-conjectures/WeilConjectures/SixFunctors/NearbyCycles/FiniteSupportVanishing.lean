/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShortcutInstances
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.FinitePointConservative

/-!

# Complexes with finite support and no global cohomology vanish

Let `k` be a separably closed field, `p : X ⟶ Spec k` locally of finite type, `Λ` any condensed
coefficient ring (for instance a finite ring `𝔽_E`) and `S` a finite set of closed points of `X`.
A complex `C` of `Λ`-modules on `X_proét` whose restriction to `X ∖ S` vanishes and whose
cohomology `Rp_* C` vanishes is zero
(`ProEtale.CondensedRing.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero`).
No constructibility or boundedness of `C` is assumed: this is the finite-support step of
Deligne's proof of the invariance of nearby cycles under change of trait (SGA 4½, [Th. finitude],
proof of 3.7), applied there to a cone not yet known to be constructible. The version on the
special fibre of a model over a trait with separably closed residue field is
`NearbyCyclesModel.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero`, and the
form for morphisms (the cone of a morphism) is
`NearbyCyclesModel.isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map`.

The bounded constructible `ℚ̄_ℓ` case is
`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens` (blueprint
`lemma-finite-support-global-sections--1`).

## Proof

This is the skyscraper decomposition. Let `i : Z ⟶ X` be the reduced closed subscheme on `S`:
it is finite over `k`, being quasi-compact and quasi-finite over a field
(`AlgebraicGeometry.IsFinite.of_finite_of_locallyOfFiniteType`). As `C` vanishes on the open
complement, the unit `C ⟶ Ri_* Li^* C` is an isomorphism, so
`R(i ≫ p)_* Li^* C ≅ Rp_* C = 0`. Derived pushforward along the finite morphism `i ≫ p` to a
separably closed point is conservative
(`ProEtale.CondensedRing.isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite`: on the finite
discrete scheme `Z`, a module is the direct sum of the pushforwards from its points, and the
pushforward between separably closed points is an equivalence), so `Li^* C = 0` and `C = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale.CondensedRing

attribute [local instance] hasTensor₄ObjExt_mod hasGoodTensor₁₂Tensor_mod hasGoodTensorTensor₂₃_mod
  hasColimitsOfShape_int_mod preservesColimitsOfShape_int_curriedTensor_obj_mod
  preservesColimitsOfShape_int_curriedTensor_flip_obj_mod

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [LocallyOfFiniteType p]

/-- **A complex with finite support and no global cohomology vanishes**: let `p : X ⟶ Spec k` be
locally of finite type, `k` separably closed, and `S` a finite set of closed points of `X`. A
complex `C` of `Λ`-modules on `X_proét`, for any coefficient ring `Λ`, whose restriction to
`X ∖ S` vanishes and with `Rp_* C = 0` is zero. Neither boundedness nor constructibility of `C` is
needed: `C ≅ Ri_* Li^* C` for the finite closed subscheme `i : Z ⟶ X` on `S`, and the derived
pushforward along the finite morphism `i ≫ p` to a separably closed point is conservative. -/
theorem isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed {x})
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hU : IsZero ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).obj C))
    (hΓ : IsZero ((R((p)_*⟦Λ⟧)).obj C)) : IsZero C := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let Z : TopologicalSpace.Closeds X :=
    ⟨S, by simpa using (finsetComplOpens S hS).isOpen.isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal Z).subschemeι
  -- the closed subscheme `Z` on `S` is finite over `k`
  have : Finite (IdealSheafData.vanishingIdeal Z).subscheme := by
    have : Finite (Set.range i) := by
      rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
      exact S.finite_toSet.to_subtype
    exact Finite.of_injective (fun z ↦ (⟨i z, z, rfl⟩ : Set.range i))
      fun a b h ↦ i.isClosedEmbedding.injective (congrArg Subtype.val h :)
  have := IsFinite.of_finite_of_locallyOfFiniteType (i ≫ p)
  have hcompl : IsCompl (Set.range i.base) (Set.range (finsetComplOpens S hS).ι.base) := by
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal,
      Scheme.Opens.range_ι, coe_finsetComplOpens]
    exact isCompl_compl
  have hunit := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (finsetComplOpens S hS).ι i hcompl hU
  -- `R(i ≫ p)_* Li^* C ≅ Rp_* Ri_* Li^* C ≅ Rp_* C = 0`
  have hZ : IsZero ((R((i ≫ p)_*⟦Λ⟧)).obj ((L((i)^*⟦Λ⟧)).obj C)) :=
    (hΓ.of_iso ((R((p)_*⟦Λ⟧)).mapIso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app C)).symm)).of_iso
      ((rightDerivedLowerStarComp Λ i p).app _).symm
  have hi : IsZero ((L((i)^*⟦Λ⟧)).obj C) := by
    have := isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite Λ (i ≫ p)
      (0 : (L((i)^*⟦Λ⟧)).obj C ⟶ 0)
      (isIso_of_source_target_iso_zero _ hZ.isoZero
        ((R((i ≫ p)_*⟦Λ⟧)).map_isZero (isZero_zero _)).isoZero)
    exact (isZero_zero _).of_iso (asIso (0 : (L((i)^*⟦Λ⟧)).obj C ⟶ 0))
  exact ((R((i)_*⟦Λ⟧)).map_isZero hi).of_iso
    (asIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app C))

/-- **Isomorphisms away from finitely many closed points, detected on cohomology**: let
`p : X ⟶ Spec k` be locally of finite type, `k` separably closed, and `S` a finite set of closed
points of `X`. A morphism `a : K ⟶ L` of complexes of `Λ`-modules on `X_proét` which is an
isomorphism on `X ∖ S` and such that `Rp_* a` is an isomorphism is an isomorphism: its cone
satisfies the hypotheses of
`ProEtale.CondensedRing.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero`. -/
theorem isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed {x})
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (a : K ⟶ L)
    (hU : IsIso ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).map a))
    (hΓ : IsIso ((R((p)_*⟦Λ⟧)).map a)) : IsIso a := by
  obtain ⟨C, b, c, hT⟩ := Pretriangulated.distinguished_cocone_triangle a
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero Λ p S hS C ?_ ?_)
  · exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).map_distinguished _ hT)).2 hU
  · exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((R((p)_*⟦Λ⟧)).map_distinguished _ hT)).2 hΓ

omit [IsSepClosed k] [LocallyOfFiniteType p] in
/-- A complex vanishes on an open `U` as soon as all its cohomology sheaves do: the derived
pullback along the open immersion is computed levelwise by the exact functor `U.ι^*`, which
commutes with cohomology. -/
lemma isZero_leftDerivedUpperStar_obj_of_forall_isZero_upperStar_homology (U : X.Opens)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hC : ∀ n : ℤ, IsZero ((U.ι)^*⟦Λ⟧.obj ((DerivedCategory.homologyFunctor _ n).obj C))) :
    IsZero ((L((U.ι)^*⟦Λ⟧)).obj C) := by
  refine (DerivedCategory.isZero_of_forall_isZero_homology _ fun n ↦ ?_).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ U.ι).app C)
  exact (hC n).of_iso (((U.ι)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app C).symm

/-- **A complex whose cohomology sheaves are supported on finitely many closed points and with no
global cohomology vanishes**: the form of
`ProEtale.CondensedRing.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero` in
which the support condition is imposed on every cohomology sheaf `Hⁿ(C)`. -/
theorem isZero_of_forall_isZero_upperStar_homology_of_isZero (S : Finset X)
    (hS : ∀ x ∈ S, IsClosed {x})
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hU : ∀ n : ℤ, IsZero (((finsetComplOpens S hS).ι)^*⟦Λ⟧.obj
      ((DerivedCategory.homologyFunctor _ n).obj C)))
    (hΓ : IsZero ((R((p)_*⟦Λ⟧)).obj C)) : IsZero C :=
  isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero Λ p S hS C
    (isZero_leftDerivedUpperStar_obj_of_forall_isZero_upperStar_homology Λ _ C hU) hΓ

end ProEtale.CondensedRing

namespace ProEtale.CondensedRing.NearbyCyclesModel

attribute [local instance] hasTensor₄ObjExt_mod hasGoodTensor₁₂Tensor_mod hasGoodTensorTensor₂₃_mod
  hasColimitsOfShape_int_mod preservesColimitsOfShape_int_curriedTensor_obj_mod
  preservesColimitsOfShape_int_curriedTensor_flip_obj_mod

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {R : Type u} [CommRing R] {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ}
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'} {q : M.total ⟶ Spec (.of R)}
  [LocallyOfFiniteType q] {p : X' ⟶ Spec (.of κ)}

/-- **The finite-support criterion on the special fibre of a model** (SGA 4½, [Th. finitude],
proof of 3.7): let `M` be a model locally of finite type over `Spec R` along `q`, whose special
fibre `p : X' ⟶ Spec κ` is the base change of `q` along `b : R ⟶ κ`, `κ` separably closed (for
instance the residue field of a strictly henselian trait). A complex `C` of `Λ`-modules on the
special fibre `X'` which vanishes away from a finite set `S` of closed points and has no
cohomology, `Rp_* C = 0`, is zero. No constructibility of `C` is assumed. -/
theorem isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero
    (hMi : IsPullback M.i p q (Spec.map (CommRingCat.ofHom b))) (S : Finset X')
    (hS : ∀ x ∈ S, IsClosed {x})
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X')))
    (hU : IsZero ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).obj C))
    (hΓ : IsZero ((R((p)_*⟦Λ⟧)).obj C)) : IsZero C :=
  have : LocallyOfFiniteType p := MorphismProperty.of_isPullback hMi inferInstance
  CondensedRing.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero Λ p S hS C hU hΓ

/-- **The finite-support criterion on the special fibre of a model, for morphisms**: in the
situation of `NearbyCyclesModel.isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero`,
a morphism `a` of complexes on the special fibre `X'` which is an isomorphism away from a finite
set of closed points and such that `Rp_* a` is an isomorphism is an isomorphism. This is the form
in which Deligne's induction applies it, to the base change morphism of a change of trait
restricted to the special fibre. -/
theorem isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map
    (hMi : IsPullback M.i p q (Spec.map (CommRingCat.ofHom b))) (S : Finset X')
    (hS : ∀ x ∈ S, IsClosed {x})
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X'))} (a : K ⟶ L)
    (hU : IsIso ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).map a))
    (hΓ : IsIso ((R((p)_*⟦Λ⟧)).map a)) : IsIso a :=
  have : LocallyOfFiniteType p := MorphismProperty.of_isPullback hMi inferInstance
  CondensedRing.isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map Λ p S hS a hU hΓ

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
