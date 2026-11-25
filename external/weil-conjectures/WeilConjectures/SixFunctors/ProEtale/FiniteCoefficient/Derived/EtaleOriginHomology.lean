/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.EssImageKernels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# Pro-étale complexes with cohomology sheaves of étale origin

Let `Λ` be a ring and `X` a scheme. The pro-étale sheaves of `Λ`-modules of étale origin (the
essential image of the comparison pullback `ν^*`, `AlgebraicGeometry.ProEtale.etaleOrigin`) form a
weak Serre class closed under coproducts: `ν^*` is exact, fully faithful and a left adjoint, and
extensions are handled by `AlgebraicGeometry.ProEtale.etaleOrigin_of_shortExact`. Hence the
complexes all of whose cohomology sheaves are of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.etaleOriginHomology`) form a localizing
subcategory of `D(X_proét, Λ)`, stable under the truncations. It contains `Dctf(X, Λ)`, hence its
localizing closure `Loc(Dctf(X, Λ))`
(`AlgebraicGeometry.ProEtale.DerivedCategory.localizingClosure_constructibleFiniteTor_le`), and
it is preserved by the extension by zero along an open immersion.

Its bounded objects are of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`): this is a
dévissage along the truncation triangles, the bounded below objects of étale origin forming a
triangulated subcategory by full faithfulness of `ν^*` on `D⁺`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

instance : (etaleOrigin (ModuleCat.{u + 1} Λ) X).ContainsZero where
  exists_zero := ⟨_, (ν^*(X)[ModuleCat.{u + 1} Λ]).map_isZero (isZero_zero _), _, ⟨Iso.refl _⟩⟩

instance : (etaleOrigin (ModuleCat.{u + 1} Λ) X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := etaleOrigin_of_shortExact hS h₁ h₃

namespace DerivedCategory

/-- The pro-étale complexes all of whose cohomology sheaves are of étale origin. -/
abbrev etaleOriginHomology :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ))) :=
  _root_.DerivedCategory.homologyProperty (etaleOrigin (ModuleCat.{u + 1} Λ) X)

variable {Λ X}

/-- The cohomology sheaves of a pro-étale complex of étale origin are of étale origin. -/
lemma etaleOriginHomology_mapDerivedCategory_obj
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    etaleOriginHomology Λ X (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) := fun n ↦
  ⟨_, ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K⟩⟩

/-- A bounded constructible pro-étale complex has cohomology sheaves of étale origin. -/
lemma etaleOriginHomology_of_boundedConstructible
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    etaleOriginHomology Λ X K := by
  obtain ⟨K', -, ⟨e⟩⟩ := hK
  exact (etaleOriginHomology Λ X).prop_of_iso e (etaleOriginHomology_mapDerivedCategory_obj K')

variable (Λ X)

/-- Complexes with cohomology sheaves of étale origin are closed under coproducts. -/
lemma etaleOriginHomology_sigma {J : Type*}
    [HasColimitsOfShape (Discrete J) (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [HasColimitsOfShape (Discrete J) (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))]
    [HasExactColimitsOfShape (Discrete J)
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))]
    (N : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hN : ∀ j, etaleOriginHomology Λ X (N j)) : etaleOriginHomology Λ X (∐ N) := fun n ↦
  (etaleOrigin (ModuleCat.{u + 1} Λ) X).prop_of_isColimit
    (isColimitOfPreserves (_root_.DerivedCategory.homologyFunctor _ n) (coproductIsCoproduct N))
    fun j ↦ hN j.as n

/-- The complexes with cohomology sheaves of étale origin form a localizing subcategory. -/
instance isLocalizing_etaleOriginHomology :
    (etaleOriginHomology Λ X).IsLocalizing where
  isClosedUnderColimitsOfShape_discrete _ := ⟨fun _ ⟨h⟩ ↦
    (etaleOriginHomology Λ X).prop_of_iso
      (h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
        (HasColimit.isoOfNatIso Discrete.natIsoFunctor) ≪≫ Iso.refl _).symm
      (etaleOriginHomology_sigma Λ X _ fun j ↦ h.prop_diag_obj ⟨j⟩)⟩

/-- `Dctf(X, Λ)` consists of complexes with cohomology sheaves of étale origin. -/
lemma constructibleFiniteTor_le_etaleOriginHomology :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ≤ etaleOriginHomology Λ X :=
  fun _ hK ↦ etaleOriginHomology_of_boundedConstructible hK.1

/-- `Loc(Dctf(X, Λ))` consists of complexes with cohomology sheaves of étale origin. -/
lemma localizingClosure_constructibleFiniteTor_le :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure ≤
      etaleOriginHomology Λ X :=
  ObjectProperty.localizingClosure_le (constructibleFiniteTor_le_etaleOriginHomology Λ X)

/-- The extension by zero along an open immersion preserves complexes with cohomology sheaves
of étale origin: `j_!` is exact and `j_! ν^* ≅ ν^* j_!`. -/
lemma etaleOriginHomology_openImmersionLowerShriek {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hK : etaleOriginHomology Λ U K) :
    etaleOriginHomology Λ X
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K) :=
  fun n ↦ by
    obtain ⟨G, ⟨e⟩⟩ := hK n
    exact ⟨(Etale.openImmersionLowerShriek _ j).obj G,
      ⟨(openImmersionLowerShriekComparisonUpperStarIso _ j).app G ≪≫
        (ProEtale.openImmersionLowerShriek _ j).mapIso e ≪≫
        ((ProEtale.openImmersionLowerShriek _ j).mapDerivedCategoryHomologyFunctorIso n).app K⟩⟩

end DerivedCategory

open _root_.DerivedCategory.TStructure (t) in
/-- The bounded below pro-étale complexes of étale origin form a triangulated subcategory: an
extension of `ν^* B` by `ν^* A` is classified by a morphism `ν^* B ⟶ (ν^* A)⟦1⟧`, which comes
from `B ⟶ A⟦1⟧` by full faithfulness of `ν^*` on `D⁺`. -/
instance isTriangulated_plusEtaleOrigin :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).IsTriangulated where
  exists_zero := ⟨_, (D(ν^*(X)[ModuleCat.{u + 1} Λ])).map_isZero (isZero_zero _), 0,
    ⟨0, inferInstance⟩, ⟨Iso.refl _⟩⟩
  isStableUnderShiftBy n := ⟨fun _ ⟨G, hG, ⟨e⟩⟩ ↦ ⟨G⟦n⟧, t.plus.le_shift n G hG,
    ⟨((D(ν^*(X)[ModuleCat.{u + 1} Λ])).commShiftIso n).app G ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT ⟨A, hA, ⟨e₁⟩⟩ ⟨B, hB, ⟨e₃⟩⟩ ↦ by
    obtain ⟨φ, hφ : D(ν^*(X)[ModuleCat.{u + 1} Λ]).map φ = _⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map B (A⟦(1 : ℤ)⟧)
        (t.plus.le_shift 1 A hA)).2
        (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).commShiftIso (1 : ℤ)).inv.app A)
    obtain ⟨Y, a, b, hT'⟩ := distinguished_cocone_triangle₂ φ
    refine ⟨Y, t.plus.ext_of_isTriangulatedClosed₂ _ hT' hA hB, ⟨Triangle.π₂.mapIso
      (isoTriangleOfIso₁₃ (Triangle.mk (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map a)
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map b) (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map φ ≫
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).commShiftIso (1 : ℤ)).hom.app A)) T
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map_distinguished _ hT') hT e₁ e₃ ?_)⟩⟩
    simp [hφ, ← Functor.map_comp]

/-- Bounded pro-étale complexes with cohomology sheaves of étale origin are of étale origin
(dévissage along the truncation triangles). -/
lemma DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.etaleOriginHomology Λ X K)
    (hb : _root_.DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K :=
  _root_.DerivedCategory.prop_of_bounded _ (etaleOrigin (ModuleCat.{u + 1} Λ) X)
    (fun _ ⟨G, ⟨e⟩⟩ ↦ ⟨(_root_.DerivedCategory.singleFunctor _ 0).obj G, ⟨0, inferInstance⟩,
      ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩) K hb hK

variable {Λ X} in
/-- If `ν^* G` lies in degrees `≥ a`, so does `G`. -/
lemma isGE_of_isGE_mapDerivedCategory_comparisonUpperStar
    {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a : ℤ}
    (h : (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G).IsGE a) : G.IsGE a :=
  (_root_.DerivedCategory.isGE_iff G a).2 fun i hi ↦
    Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (ν^*(X)[ModuleCat.{u + 1} Λ])
      ((_root_.DerivedCategory.isGE_iff _ a).1 h i hi)

variable {Λ X} in
/-- If `ν^* G` lies in degrees `≤ b`, so does `G`. -/
lemma isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
    {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {b : ℤ}
    (h : (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G).IsLE b) : G.IsLE b :=
  (_root_.DerivedCategory.isLE_iff G b).2 fun i hi ↦
    Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (ν^*(X)[ModuleCat.{u + 1} Λ])
      ((_root_.DerivedCategory.isLE_iff _ b).1 h i hi)

end AlgebraicGeometry.ProEtale
