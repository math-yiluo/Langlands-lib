/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyTensorColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Monoidal

/-!

# Cohomology of a tensor product along a filtered system, field coefficients

Let `T₀` be a finite discrete field and `Λ = C(-, T₀)`. Every module object over `Λ_Z` on
`Z_proét` is flat (`ProEtale.CondensedRing.flat_of_isField`): the comparison
`ProEtale.finiteCoefficientModEquivalence` with pro-étale sheaves of `T₀`-vector spaces commutes
with the tensor products, and sheaves of vector spaces are flat (`Sheaf.flat_of_field`).

Hence, for a filtered family `Y_j ⟶ Y` of uniformly bounded below complexes of `Λ`-module
objects on `Z_proét` whose cohomology sheaves are colimits, and a bounded below `W`, the
cohomology sheaves of `Y_j ⊗ᴸ W` have colimit those of `Y ⊗ᴸ W`
(`ProEtale.CondensedRing.isColimit_homology_tensorRight_mapCocone`, an instance of
`DerivedCategory.nonempty_isColimit_homologyFunctor_tensorRight_mapCocone`), also for families
given by a functor `G₀` applied to a cocone
(`ProEtale.CondensedRing.isColimit_homology_tensorRight_mapCocone'`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.ObjectProperty

variable {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Flatness is reflected by an equivalence commuting with the tensor products: if
`E (M ⊗ N) ≅ E M ⊗ E N` naturally in `M` and `N` and `E M` is flat, then `M` is flat. -/
lemma flat_of_flat_functor_obj (E : A ≌ B)
    (e : (Functor.postcompose₂.obj E.functor).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ _).obj E.functor).obj E.functor).obj (curriedTensor B))
    {M : A} (hM : flat (E.functor.obj M)) : flat M := by
  have : PreservesFiniteLimits (tensorLeft (E.functor.obj M)) := hM.tensorLeft.1
  have : PreservesFiniteColimits (tensorLeft (E.functor.obj M)) := hM.tensorLeft.2
  have : PreservesFiniteLimits (tensorRight (E.functor.obj M)) := hM.tensorRight.1
  have : PreservesFiniteColimits (tensorRight (E.functor.obj M)) := hM.tensorRight.2
  let eL : tensorLeft M ≅ (E.functor ⋙ tensorLeft (E.functor.obj M)) ⋙ E.inverse :=
    (Functor.rightUnitor (tensorLeft M)).symm ≪≫ Functor.isoWhiskerLeft _ E.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e.app M) E.inverse
  let eR : tensorRight M ≅ (E.functor ⋙ tensorRight (E.functor.obj M)) ⋙ E.inverse :=
    (Functor.rightUnitor (tensorRight M)).symm ≪≫ Functor.isoWhiskerLeft _ E.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (NatIso.ofComponents (fun N ↦ (e.app N).app M)
          (fun {N N'} f ↦ NatTrans.congr_app (e.hom.naturality f) M)) E.inverse
  exact ⟨⟨preservesFiniteLimits_of_natIso eL.symm, preservesFiniteColimits_of_natIso eL.symm⟩,
    ⟨preservesFiniteLimits_of_natIso eR.symm, preservesFiniteColimits_of_natIso eR.symm⟩⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T₀ : Type) [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
  [Finite T₀]

/-- Over a finite discrete field `T₀`, every module object over `C(-, T₀)_Z` on `Z_proét` is
flat: through `ProEtale.finiteCoefficientModEquivalence`, which commutes with the tensor
products, it is a sheaf of `T₀`-vector spaces. -/
theorem flat_of_isField {Z : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) :
    ObjectProperty.flat M :=
  ObjectProperty.flat_of_flat_functor_obj _ (finiteCoefficientModEquivalenceTensorIso Z T₀)
    (Sheaf.flat_of_field _ _)

/-- **The cohomology sheaves of a tensor product with a bounded below complex commute with
filtered colimits in the first variable**, with coefficients a finite field: for a filtered
cocone `c` of complexes of `C(-, T₀)`-module objects vanishing in degrees `< a` whose cohomology
sheaves are colimits and a bounded below `W`, the cohomology sheaves of `c ⊗ᴸ W` are colimits. -/
theorem isColimit_homology_tensorRight_mapCocone {Z : Scheme.{u}} {J : Type u}
    [SmallCategory J] [IsFiltered J]
    {F : J ⥤ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))} (c : Cocone F) (a : ℤ)
    (hF : ∀ j, (F.obj j).IsGE a) (hc : c.pt.IsGE a)
    (hH : ∀ p, IsColimit ((DerivedCategory.homologyFunctor _ p).mapCocone c))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (b : ℤ) (hW : W.IsGE b)
    (q : ℤ) :
    Nonempty (IsColimit ((tensorRight W ⋙ DerivedCategory.homologyFunctor _ q).mapCocone c)) := by
  have : AB5OfSize.{u, u} (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z)) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  exact DerivedCategory.nonempty_isColimit_homologyFunctor_tensorRight_mapCocone
    (flat_of_isField T₀) a hF hc (fun p ↦ ⟨hH p⟩) W b q

/-- Variant of `ProEtale.CondensedRing.isColimit_homology_tensorRight_mapCocone` for the image
of a filtered cocone `c` under a functor `G₀` to the derived category. -/
theorem isColimit_homology_tensorRight_mapCocone' {Z : Scheme.{u}} {J : Type u}
    [SmallCategory J] [IsFiltered J] {C₀ : Type*} [Category C₀] {F : J ⥤ C₀} (c : Cocone F)
    (G₀ : C₀ ⥤ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (a : ℤ)
    (hF : ∀ j, (G₀.obj (F.obj j)).IsGE a) (hc : (G₀.obj c.pt).IsGE a)
    (hH : ∀ p, IsColimit ((G₀ ⋙ DerivedCategory.homologyFunctor _ p).mapCocone c))
    (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Z))) (b : ℤ) (hW : W.IsGE b)
    (q : ℤ) :
    Nonempty (IsColimit ((G₀ ⋙ tensorRight W ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
      c)) :=
  (isColimit_homology_tensorRight_mapCocone T₀ (G₀.mapCocone c) a hF hc
    (fun p ↦ IsColimit.ofIsoColimit (hH p) (Functor.mapCoconeMapCocone c).symm) W b hW q).map
    fun h ↦ IsColimit.ofIsoColimit h (Functor.mapCoconeMapCocone c)

end AlgebraicGeometry.ProEtale.CondensedRing
