/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb

/-!
# The derived closed pullback of module objects preserves countable products

Let `Λ` be a commutative condensed ring, `X` a quasi-compact quasi-separated scheme and
`i : Z ⟶ X` a closed immersion with quasi-compact open complement `j : U ⟶ X`. The derived
pullback `Li^* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Z})` on module objects preserves countable products
(`AlgebraicGeometry.ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl`).

Indeed, the pullback `i^*` of abelian pro-étale sheaves preserves all limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab_of_isCompl`), hence so does its
transport `mapMod(i^*)` to module objects, and the module pullback `(i)^*⟦Λ⟧` is `mapMod(i^*)`
followed by the extension of scalars along an isomorphism, i.e. a restriction of scalars. The
module pullback is exact, so `Li^*` is the levelwise functor `D((i)^*⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`); since
countable products of module objects are exact (repleteness,
`AlgebraicGeometry.ProEtale.CondensedRing.countableAB4Star_mod`), derived countable products are
computed degreewise and are preserved by the levelwise functor
(`CategoryTheory.Functor.preservesLimitsOfShape_discrete_mapDerivedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- For `X` quasi-compact and quasi-separated and `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`, the pullback `i^*` of module objects over `Λ` preserves
countable products: it is `mapMod(i^*)`, which preserves limits, followed by the extension of
scalars along an isomorphism, which is a restriction of scalars. -/
theorem preservesLimitsOfShape_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesLimitsOfShape (Discrete ℕ) (i)^*⟦Λ⟧ :=
  have := preservesLimitsOfSize_upperStar_ab_of_isCompl i j hij
  have : PreservesLimitsOfShape (Discrete ℕ) ((i)^*[Ab.{u + 1}]) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  preservesLimitsOfShape_of_natIso (Functor.isoWhiskerLeft
    ((i)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ i))).symm

/-- For `X` quasi-compact and quasi-separated and `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`, the derived pullback `Li^* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Z})` on
module objects over `Λ` preserves countable products. -/
theorem preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesLimitsOfShape (Discrete ℕ) L((i)^*⟦Λ⟧) :=
  have := preservesLimitsOfShape_upperStar_of_isCompl Λ i j hij
  have := (i)^*⟦Λ⟧.preservesLimitsOfShape_discrete_mapDerivedCategory (β := ℕ)
  preservesLimitsOfShape_of_natIso (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm

/-- For `X` quasi-compact and quasi-separated and `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`, the derived pullback `Li^*` on module objects over `Λ`
preserves the countable product of copies of a single object `K`. -/
theorem preservesLimit_leftDerivedUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    PreservesLimit (Discrete.functor fun _ : ℕ ↦ K) L((i)^*⟦Λ⟧) :=
  have := preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl Λ i j hij
  inferInstance

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- On a noetherian scheme, the derived pullback `Li^*` along a closed immersion preserves
countable products: the open complement of `i` is quasi-compact. -/
theorem preservesLimitsOfShape_leftDerivedUpperStar_of_isClosedImmersion [IsNoetherian X] :
    PreservesLimitsOfShape (Discrete ℕ) L((i)^*⟦Λ⟧) := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl Λ i V.ι (by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl)

end AlgebraicGeometry.ProEtale.CondensedRing
