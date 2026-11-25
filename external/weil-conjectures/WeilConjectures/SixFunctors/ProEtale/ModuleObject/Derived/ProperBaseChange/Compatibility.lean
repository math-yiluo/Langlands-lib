/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers

/-! # Bounded-below coefficient pushforward compatibility

The finite-to-algebraic-closure comparison is invertible on bounded-below inputs,
using scalar-basis decompositions and bounded-below copower continuity.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Mod

private theorem restrictionReflectsIsomorphisms
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    (comap (D := C) φ).ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro M N f hf
  have : IsIso f.hom := by
    change IsIso ((forget R).map ((comap φ).map f))
    infer_instance
  have : IsIso ((forget S).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (forget S)

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

private theorem isIso_mate_pushHomOfComapIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} (κ : G' ⋙ U' ≅ U ⋙ G) :
    IsIso (mateEquiv adj adj' (pushHomOfComapIso adj adj' κ)) := by
  change IsIso ((mateEquiv adj adj') ((mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ κ.inv)))
  rw [Equiv.apply_symm_apply]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction upperStarFromPoint ProEtale.upperStar

private theorem reflectsDerivedIsomorphisms
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem centralUnitCopower
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc fun i ↦
      (show M ⟶ U.obj (L.obj M) from adj.unit.app M) ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc fun i ↦
      (show G.obj M ⟶ U'.obj (L'.obj (G.obj M)) from adj'.unit.app (G.obj M)) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  have := hC
  have := hD
  apply (Adjunction.isIso_iff_unitCoproductComparison adj adj' β hκ M I
    (fun i ↦ (τ i).app _) (fun i ↦ (τ' i).app _) (fun i ↦ ?_)).2 hc
  exact ((τ' i).naturality (β.app M)).symm.trans
    (congrArg (fun g ↦ β.app M ≫ g) (hs i (L.obj M))).symm

private theorem centralUnitCopowerExplicit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
      adj.unit.app M ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc (f := fun _ : I ↦ G.obj M) fun i ↦
      adj'.unit.app (G.obj M) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  exact centralUnitCopower adj adj' β hκ M I τ τ' hs hC hD hc

private theorem coefficientDerivedCoproducts (Λ : Sheaf
    (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z))) := by
  let C := Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete J)
  exact CategoryTheory.derived_hasCoproducts

-- The explicit mate and coproduct comparison are elaborated in several large derived categories.
/-- **(Push)** for `E ⊆ ℚ̄_ℓ` is invertible at every bounded-below complex when `f` is proper.
Source: the finite-support coefficient model and bounded-below coproduct continuity.
(blueprint: lem-weil-pbc-condensed-qbar-bounded-push)

Proof: choose the compatible scalar-basis decompositions of both extension units. The mate
of the canonical push comparison is the inverse restriction/pushforward isomorphism.
Restriction reflects derived isomorphisms, by exactness and the homology criterion.
The unit-mate calculation identifies the restricted component, conjugated by the two basis
isomorphisms, with the copower comparison followed by invertible factors. The copies of the
input complex have the same lower bound. Bounded-below copower continuity for the proper,
hence qcqs, map makes this comparison invertible. Reflection gives the conclusion.
This does not assert an isomorphism of functors on the ambient unbounded categories. -/
theorem isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE [IsProper f]
    (E : FiniteIntermediateField ℓ)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (N : ℤ) [M.IsGE N] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M) := by
  classical
  have hb := condensedQbar_derived_scalar_basis.{u} ℓ E
  unfold CondensedQbarDerivedScalarBasis at hb
  rcases hb with ⟨I, τ, hunit, hscalar⟩
  have hcomm (Z : Scheme.{u}) : IsCommMonObj (padicSubfieldRingObj Z ℓ E) :=
    isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj E) Z
  have : HasCoproduct (fun _ : I ↦ M) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) X I).has_colimit _
  have : HasCoproduct (fun _ : I ↦ R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj M) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) Y I).has_colimit _
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)).ReflectsIsomorphisms :=
    Mod.restrictionReflectsIsomorphisms (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          Y)).mapDerivedCategory.ReflectsIsomorphisms :=
    reflectsDerivedIsomorphisms _
  have hκ : IsIso
      (mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
          (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)) := by
    unfold derivedPushHom
    exact Adjunction.isIso_mate_pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
      (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
  refine centralUnitCopowerExplicit
    (G := R((f)_*⟦Profinite.continuousMapRingObj E⟧)
    ) (G' := R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
    (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) hκ M I
    (τ X) (τ Y) ?_ ?_ ?_ ?_
  · exact fun i K ↦ hscalar f i K
  · exact hunit X M
  · exact hunit Y (R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj M)
  · exact condensedSubfield_bounded_copower_comparison.{u} ℓ E f I M N

end AlgebraicGeometry.ProEtale.CondensedRing
