/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Transport of finiteness along an isomorphism of coefficient rings

Let `e : Λ ≅ Λ'` be an isomorphism of commutative condensed rings. The restriction of scalars
along the induced isomorphisms `a_X : Λ_X ≅ Λ'_X` identifies the sheaves of `Λ'`-modules with the
sheaves of `Λ`-modules on `X_proét`. This file records that this identification is compatible
with the finiteness conditions and with the derived pushforward, so that finiteness statements
for `Rp_*` may be transported from `Λ'` to `Λ`.

## Main results

* `ProEtale.isConstructibleModuleObject_comap_iff`: the restriction of scalars along an
  isomorphism of ring objects preserves and reflects constructibility.
* `ProEtale.boundedConstructible_mapDerivedCategory_comap_iff`: it preserves and reflects
  bounded constructible complexes.
* `ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_iso`: if `Rp_*` preserves
  bounded constructible complexes for the coefficients `Λ'`, it does for `Λ`.
* `ProEtale.CondensedRing.isLE_rightDerivedLowerStar_singleFunctor_of_iso`: an amplitude bound
  for `Rp_*` on constructible sheaves transports from `Λ'` to `Λ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section ComapIso

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [MonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- The restriction of scalars along an isomorphism of ring objects preserves and reflects
pro-étale local finite presentation. -/
lemma isLocallyFinitelyPresented_comap_iff
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj N) ↔ IsLocallyFinitelyPresented S N := by
  refine ⟨fun ⟨𝒰, h⟩ ↦ ⟨𝒰, fun i ↦ ?_⟩, fun ⟨𝒰, h⟩ ↦ ⟨𝒰, fun i ↦ ?_⟩⟩
  · exact ((h i).of_iso
      (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app N)).of_comap _
  · exact ((h i).comap ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).map φ)).of_iso
      (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app N).symm

/-- The restriction of scalars along an isomorphism of ring objects preserves and reflects
constructibility. -/
lemma isConstructibleModuleObject_comap_iff
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj N) ↔ IsConstructibleModuleObject S N := by
  refine ⟨fun ⟨𝒮, h⟩ ↦ ⟨𝒮, fun a ↦ ?_⟩, fun ⟨𝒮, h⟩ ↦ ⟨𝒮, fun a ↦ ?_⟩⟩
  · exact (isLocallyFinitelyPresented_comap_iff
      ((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).map φ) _).1 ((h a).of_iso
        (((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).mapModComapIso φ).app N))
  · exact ((isLocallyFinitelyPresented_comap_iff
      ((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).map φ) _).2 (h a)).of_iso
        (((ProEtale.upperStar Ab.{u + 1} (𝒮.immersion a)).mapModComapIso φ).app N).symm

/-- The derived restriction of scalars along an isomorphism of ring objects preserves and
reflects bounded constructible complexes. -/
lemma boundedConstructible_mapDerivedCategory_comap_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)) :
    boundedConstructible R ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible S K := by
  refine and_congr ⟨(Mod.comap φ).bounded_of_bounded_mapDerivedCategory_obj,
    (Mod.comap φ).bounded_mapDerivedCategory_obj⟩ (forall_congr' fun n ↦ ?_)
  rw [← isConstructibleModuleObject_comap_iff φ]
  exact ⟨fun h ↦ h.of_iso (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K).symm,
    fun h ↦ h.of_iso (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K)⟩

omit [IsIso φ] in
/-- The derived restriction of scalars reflects the upper bounds for the canonical
t-structure, being faithful and exact. -/
lemma isLE_of_isLE_mapDerivedCategory_comap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)) (d : ℤ)
    (h : ((Mod.comap φ).mapDerivedCategory.obj K).IsLE d) : K.IsLE d :=
  (DerivedCategory.isLE_iff K d).2 fun i hi ↦
    (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isLE_iff _ d).1 h i hi)

end ComapIso

namespace CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ']

omit [IsCommMonObj Λ'] in
/-- The extension of scalars along the coefficient change induced by an isomorphism of condensed
rings is left exact, being isomorphic to a restriction of scalars. It is not an instance: the
search for `IsIso a` would be attempted for every coefficient change. -/
lemma preservesFiniteLimits_extendScalars_coefficientMap_of_isIso (a : Λ ⟶ Λ')
    [IsMonHom a] [IsIso a] (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X)) :=
  preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- Restriction of scalars along an isomorphism of coefficient rings preserves and reflects
constructibility. -/
theorem isConstructibleModuleObject_comap_coefficientMap_iff (e : Λ ≅ Λ') [IsMonHom e.hom]
    {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X)
        ((Mod.comap (coefficientMap e.hom X)).obj M) ↔
      IsConstructibleModuleObject (condensedRingObj Λ' X) M :=
  isConstructibleModuleObject_comap_iff _ M

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- Restriction of scalars along an isomorphism of coefficient rings preserves and reflects
bounded constructible complexes. -/
theorem boundedConstructible_mapDerivedCategory_comap_coefficientMap_iff (e : Λ ≅ Λ')
    [IsMonHom e.hom] {X : Scheme.{u}}
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) :
    boundedConstructible (condensedRingObj Λ X)
        ((Mod.comap (coefficientMap e.hom X)).mapDerivedCategory.obj K) ↔
      boundedConstructible (condensedRingObj Λ' X) K :=
  boundedConstructible_mapDerivedCategory_comap_iff _ K

omit [IsCommMonObj Λ] in
/-- Transport of the finiteness of `Rp_*` along an isomorphism of coefficient rings. -/
theorem boundedConstructible_rightDerivedLowerStar_of_iso (e : Λ ≅ Λ') [IsMonHom e.hom]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (h : ∀ K, boundedConstructible (condensedRingObj Λ' Z) K →
      boundedConstructible (condensedRingObj Λ' Y) ((R((p)_*⟦Λ'⟧)).obj K))
    (K) (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    boundedConstructible (condensedRingObj Λ Y) ((R((p)_*⟦Λ⟧)).obj K) := by
  have := fun X : Scheme.{u} ↦ preservesFiniteLimits_extendScalars_coefficientMap_of_isIso e.inv X
  rw [← boundedConstructible_mapDerivedCategory_comap_iff (coefficientMap e.inv Y)]
  exact (boundedConstructible _).prop_of_iso ((derivedComapLowerStarIso e.inv p).app K).symm
    (h _ ((boundedConstructible_mapDerivedCategory_comap_iff _ K).2 hK))

omit [IsCommMonObj Λ] in
/-- Transport of an amplitude bound for `Rp_*` on constructible sheaves along an isomorphism of
coefficient rings. -/
theorem isLE_rightDerivedLowerStar_singleFunctor_of_iso (e : Λ ≅ Λ') [IsMonHom e.hom]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) (d : ℤ)
    (h : ∀ N, IsConstructibleModuleObject (condensedRingObj Λ' Z) N →
      (R((p)_*⟦Λ'⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d)
    (N) (hN : IsConstructibleModuleObject (condensedRingObj Λ Z) N) :
    (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d := by
  have := fun X : Scheme.{u} ↦ preservesFiniteLimits_extendScalars_coefficientMap_of_isIso e.inv X
  refine isLE_of_isLE_mapDerivedCategory_comap (coefficientMap e.inv Y) _ d ?_
  have : (R((p)_*⟦Λ'⟧).obj ((Mod.comap (coefficientMap e.inv Z) ⋙
      DerivedCategory.singleFunctor _ 0).obj N)).IsLE d :=
    h _ ((isConstructibleModuleObject_comap_iff (coefficientMap e.inv Z) N).2 hN)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (R((p)_*⟦Λ'⟧).mapIso (((Mod.comap (coefficientMap e.inv Z)).mapDerivedCategorySingleFunctor
      0).app N).symm ≪≫ ((derivedComapLowerStarIso e.inv p).app _).symm) d

end CondensedRing

end AlgebraicGeometry.ProEtale
