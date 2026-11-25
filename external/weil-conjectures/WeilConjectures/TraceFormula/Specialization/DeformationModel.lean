/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap
public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# The deformation to the normal cone as a model over a trait

Let `X` be a scheme over a field `k`, `I` an ideal sheaf on `X`, and `k'` an extension of `k`.
Following Varshavsky (*Lefschetz–Verdier trace formula and a generalization of a theorem of
Fujiwara*, §1.4–§2), we base change the deformation space `D_I X ⟶ 𝔸¹_k` along the coordinate
`t : S = Spec k'⟦t⟧ ⟶ 𝔸¹_k` (`AlgebraicGeometry.traitToAffineLine`). This gives a scheme
```
𝒳 = D_I X ×_{𝔸¹_k} S ⟶ S
```
over the trait (`AlgebraicGeometry.ProEtale.CondensedRing.deformationTotal`). Its geometric generic
fibre `𝒳 ×_S Spec Ω` maps to `X` (over the punctured line `D_I X` is `X × 𝔾_m`), and its special
fibre `𝒳 ×_S Spec k'` is the base change to `k'` of the normal cone `N_I X`, a `k'`-scheme
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationSpecialFibre`). Together they form a
nearby cycles model of `X` (`AlgebraicGeometry.ProEtale.CondensedRing.deformationModel`).

The construction is functorial in `(X, I)` for morphisms `f : X ⟶ Y` with `f^* I ⊆ J`
(`AlgebraicGeometry.ProEtale.CondensedRing.deformationModelHom`), and for a rational point `x` of
`X` and `I` its ideal, the special fibre has the `k'`-point given by the vertex of the tangent
cone at `x` (`AlgebraicGeometry.ProEtale.CondensedRing.deformationVertex`).

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.deformationSpaceToAffineLine`: `D_I X ⟶ 𝔸¹_k`.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationTotal`: the total space `𝒳`.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationGeneric`: the geometric generic fibre.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationSpecialFibre`: the special fibre, an object
  of `Over (Spec (.of k'))`; it is locally of finite type, quasi-compact and separated over `k'`
  when `X` is so over `k`.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationModel`: the nearby cycles model.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationSpecialFibreMap`,
  `AlgebraicGeometry.ProEtale.CondensedRing.deformationModelHom`: functoriality.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationVertex`: the vertex of the tangent cone at a
  rational point.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

section Model

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The coordinate `t : D_I X ⟶ 𝔸¹_k` of the deformation space of `X` over `k`. -/
noncomputable def deformationSpaceToAffineLine :
    I.deformationSpace ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  I.deformationSpaceToPolynomialSpec ≫ X.left.polynomialSpecToAffineSpace ≫
    AffineSpace.map _ X.hom

/-- The total space `𝒳 = D_I X ×_{𝔸¹_k} Spec k'⟦t⟧` of the deformation to the normal cone over the
trait. -/
noncomputable def deformationTotal : Scheme.{u} :=
  pullback (deformationSpaceToAffineLine X I) (traitToAffineLine k k')

/-- The projection `𝒳 ⟶ D_I X`. -/
noncomputable def deformationTotalToSpace : deformationTotal X I k' ⟶ I.deformationSpace :=
  pullback.fst _ _

/-- The structure morphism `𝒳 ⟶ Spec k'⟦t⟧` of the total space. -/
noncomputable def deformationTotalToTrait : deformationTotal X I k' ⟶ trait k' :=
  pullback.snd _ _

/-- The total space is the base change of the deformation space along the trait. -/
lemma isPullback_deformationTotal :
    IsPullback (deformationTotalToSpace X I k') (deformationTotalToTrait X I k')
      (deformationSpaceToAffineLine X I) (traitToAffineLine k k') :=
  IsPullback.of_hasPullback _ _

/-- The projection `𝒳 ⟶ D_I X ⟶ X` of the total space to `X`. -/
noncomputable def deformationTotalToBase : deformationTotal X I k' ⟶ X.left :=
  deformationTotalToSpace X I k' ≫ I.deformationSpaceProj

/-- The projections of the total space to `X` and to the trait agree over `Spec k`. -/
@[reassoc]
lemma deformationTotalToBase_hom :
    deformationTotalToBase X I k' ≫ X.hom = deformationTotalToTrait X I k' ≫ traitToBase k k' := by
  rw [deformationTotalToBase, Category.assoc,
    ← IdealSheafData.deformationSpaceProj_over' I X.hom, ← deformationSpaceToAffineLine,
    reassoc_of% (isPullback_deformationTotal X I k').w, traitToAffineLine_over]

/-- The geometric generic fibre `𝒳 ×_S Spec Ω` of the total space. -/
noncomputable def deformationGeneric : Scheme.{u} :=
  pullback (deformationTotalToTrait X I k') (traitGenericPoint k')

/-- The inclusion `j : 𝒳_Ω ⟶ 𝒳` of the geometric generic fibre. -/
noncomputable def deformationGenericToTotal : deformationGeneric X I k' ⟶ deformationTotal X I k' :=
  pullback.fst _ _

/-- The special fibre `𝒳 ×_S Spec k'` of the total space, as a `k'`-scheme. It is the base change
to `k'` of the normal cone `N_I X`. -/
noncomputable def deformationSpecialFibre : Over (Spec (.of k')) :=
  Over.mk (pullback.snd (deformationTotalToTrait X I k') (traitClosedPoint k'))

/-- The inclusion `i : 𝒳_s ⟶ 𝒳` of the special fibre. -/
noncomputable def deformationSpecialToTotal :
    (deformationSpecialFibre X I k').left ⟶ deformationTotal X I k' :=
  pullback.fst _ _

/-- The special fibre is the fibre of the total space over the closed point of the trait. -/
lemma isPullback_deformationSpecialFibre :
    IsPullback (deformationSpecialToTotal X I k') (deformationSpecialFibre X I k').hom
      (deformationTotalToTrait X I k') (traitClosedPoint k') :=
  IsPullback.of_hasPullback _ _

/-- The deformation to the normal cone of `I`, base changed to the trait `Spec k'⟦t⟧`, as a nearby
cycles model of `X`: the total space `𝒳 = D_I X ×_{𝔸¹_k} Spec k'⟦t⟧`, its geometric generic
fibre, its special fibre, and `ε : 𝒳_Ω ⟶ 𝒳 ⟶ D_I X ⟶ X`. -/
noncomputable def deformationModel : NearbyCyclesModel X.left (deformationSpecialFibre X I k').left
    where
  total := deformationTotal X I k'
  generic := deformationGeneric X I k'
  j := deformationGenericToTotal X I k'
  i := deformationSpecialToTotal X I k'
  ε := deformationGenericToTotal X I k' ≫ deformationTotalToBase X I k'

@[simp]
lemma deformationModel_total : (deformationModel X I k').total = deformationTotal X I k' :=
  rfl

@[simp]
lemma deformationModel_generic : (deformationModel X I k').generic = deformationGeneric X I k' :=
  rfl

@[simp]
lemma deformationModel_j : (deformationModel X I k').j = deformationGenericToTotal X I k' :=
  rfl

@[simp]
lemma deformationModel_i : (deformationModel X I k').i = deformationSpecialToTotal X I k' :=
  rfl

lemma deformationModel_ε : (deformationModel X I k').ε =
    deformationGenericToTotal X I k' ≫ deformationTotalToBase X I k' :=
  rfl

end Model

/-! ### Finiteness of the special fibre -/

section Finiteness

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The deformation space is affine over the relative affine line. -/
instance isAffineHom_deformationSpaceToPolynomialSpec :
    IsAffineHom I.deformationSpaceToPolynomialSpec := by
  have : IsAffineHom (I.deformationSpaceToPolynomialSpec ≫ X.left.polynomialSpecProj) := by
    rw [IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase _ _ _ I.toPolynomialPresheaf_comp_polynomialToRees]
    infer_instance
  exact IsAffineHom.of_comp _ X.left.polynomialSpecProj

instance [IsSeparated X.hom] : IsSeparated (deformationSpaceToAffineLine X I) := by
  have : IsSeparated (AffineSpace.map (ULift.{u} (Fin 1)) X.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (AffineSpace.isPullback_map X.hom).flip
      inferInstance
  rw [deformationSpaceToAffineLine]
  infer_instance

instance [QuasiCompact X.hom] : QuasiCompact (deformationSpaceToAffineLine X I) := by
  have : QuasiCompact (AffineSpace.map (ULift.{u} (Fin 1)) X.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (AffineSpace.isPullback_map X.hom).flip
      inferInstance
  rw [deformationSpaceToAffineLine]
  infer_instance

/-- The deformation space of a scheme locally of finite type over `k` is locally of finite type
over `𝔸¹_k`: the extended Rees algebras of the (finitely generated) ideals of a noetherian ring are
finitely generated algebras. -/
instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (deformationSpaceToAffineLine X I) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : LocallyOfFiniteType (I.deformationSpaceToPolynomialSpec ≫ X.left.polynomialSpecProj) := by
    rw [IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase _ _ _ I.toPolynomialPresheaf_comp_polynomialToRees]
    infer_instance
  have : LocallyOfFiniteType I.deformationSpaceToPolynomialSpec :=
    locallyOfFiniteType_of_comp _ X.left.polynomialSpecProj
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin 1)) X.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (AffineSpace.isPullback_map X.hom).flip inferInstance
  rw [deformationSpaceToAffineLine]
  infer_instance

instance [IsSeparated X.hom] : IsSeparated (deformationTotalToTrait X I k') :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [QuasiCompact X.hom] : QuasiCompact (deformationTotalToTrait X I k') :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (deformationTotalToTrait X I k') :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [IsSeparated X.hom] : IsSeparated (deformationSpecialFibre X I k').hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [QuasiCompact X.hom] : QuasiCompact (deformationSpecialFibre X I k').hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (deformationSpecialFibre X I k').hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

end Finiteness

/-! ### Functoriality -/

section Map

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')
  (k' : Type u) [Field k'] [Algebra k k']

/-- The morphism of deformation spaces `D_J X ⟶ D_I Y` is compatible with the coordinates
`t : D ⟶ 𝔸¹_k`. -/
@[reassoc]
lemma deformationSpaceMap_deformationSpaceToAffineLine :
    IdealSheafData.deformationSpaceMap f.left I J hJ ≫ deformationSpaceToAffineLine Y I =
      deformationSpaceToAffineLine X J := by
  rw [deformationSpaceToAffineLine, IdealSheafData.deformationSpaceMap_proj f.left I J hJ Y.hom
    X.hom (𝟙 _) (by rw [Category.comp_id]; exact Over.w f), AffineSpace.map_id, Category.comp_id,
    deformationSpaceToAffineLine]

/-- The morphism of total spaces `𝒳 ⟶ 𝒴` induced by `f : X ⟶ Y` with `f^* I ⊆ J`. -/
noncomputable def deformationTotalMap : deformationTotal X J k' ⟶ deformationTotal Y I k' :=
  pullback.map _ _ _ _ (IdealSheafData.deformationSpaceMap f.left I J hJ) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationSpaceMap_deformationSpaceToAffineLine])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma deformationTotalMap_toSpace :
    deformationTotalMap f hJ k' ≫ deformationTotalToSpace Y I k' =
      deformationTotalToSpace X J k' ≫ IdealSheafData.deformationSpaceMap f.left I J hJ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalMap_toTrait :
    deformationTotalMap f hJ k' ≫ deformationTotalToTrait Y I k' =
      deformationTotalToTrait X J k' :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The total space `𝒳` of the deformation of `J` is the base change of the total space `𝒴` of
the deformation of `I` along the morphism of deformation spaces `D_J X ⟶ D_I Y`:
```
 𝒳   ⟶   𝒴
 │        │
D_J X ⟶ D_I Y
```
-/
lemma isPullback_deformationTotalMap_toSpace :
    IsPullback (deformationTotalMap f hJ k') (deformationTotalToSpace X J k')
      (deformationTotalToSpace Y I k') (IdealSheafData.deformationSpaceMap f.left I J hJ) :=
  IsPullback.of_right (by
      rw [deformationTotalMap_toTrait, deformationSpaceMap_deformationSpaceToAffineLine]
      exact (isPullback_deformationTotal X J k').flip)
    (deformationTotalMap_toSpace f hJ k') (isPullback_deformationTotal Y I k').flip

@[reassoc (attr := simp)]
lemma deformationTotalMap_toBase :
    deformationTotalMap f hJ k' ≫ deformationTotalToBase Y I k' =
      deformationTotalToBase X J k' ≫ f.left := by
  rw [deformationTotalToBase, deformationTotalMap_toSpace_assoc,
    IdealSheafData.deformationSpaceMap_toBase, deformationTotalToBase, Category.assoc]

/-- The morphism of geometric generic fibres `𝒳_Ω ⟶ 𝒴_Ω`. -/
noncomputable def deformationGenericMap : deformationGeneric X J k' ⟶ deformationGeneric Y I k' :=
  pullback.map _ _ _ _ (deformationTotalMap f hJ k') (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationTotalMap_toTrait])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma deformationGenericMap_toTotal :
    deformationGenericMap f hJ k' ≫ deformationGenericToTotal Y I k' =
      deformationGenericToTotal X J k' ≫ deformationTotalMap f hJ k' :=
  pullback.lift_fst _ _ _

/-- The morphism of special fibres `𝒳_s ⟶ 𝒴_s` over `k'`. -/
noncomputable def deformationSpecialFibreMap :
    deformationSpecialFibre X J k' ⟶ deformationSpecialFibre Y I k' :=
  Over.homMk (pullback.map _ _ _ _ (deformationTotalMap f hJ k') (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, deformationTotalMap_toTrait])
    (by rw [Category.comp_id, Category.id_comp]))
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

@[reassoc (attr := simp)]
lemma deformationSpecialFibreMap_toTotal :
    (deformationSpecialFibreMap f hJ k').left ≫ deformationSpecialToTotal Y I k' =
      deformationSpecialToTotal X J k' ≫ deformationTotalMap f hJ k' :=
  pullback.lift_fst _ _ _

/-- The special fibre `𝒳_s` of the deformation of `J` is the base change of the special fibre
`𝒴_s` of the deformation of `I` along the morphism of total spaces `𝒳 ⟶ 𝒴`:
```
𝒳_s ⟶ 𝒴_s
 │      │
 𝒳  ⟶  𝒴
```
-/
lemma isPullback_deformationSpecialFibreMap_toTotal :
    IsPullback (deformationSpecialFibreMap f hJ k').left (deformationSpecialToTotal X J k')
      (deformationSpecialToTotal Y I k') (deformationTotalMap f hJ k') :=
  IsPullback.of_right (by
      rw [Over.w (deformationSpecialFibreMap f hJ k'), deformationTotalMap_toTrait]
      exact (isPullback_deformationSpecialFibre X J k').flip)
    (deformationSpecialFibreMap_toTotal f hJ k') (isPullback_deformationSpecialFibre Y I k').flip

/-- The morphism of nearby cycles models induced by `f : X ⟶ Y` with `f^* I ⊆ J`. -/
noncomputable def deformationModelHom :
    (deformationModel X J k').Hom (deformationModel Y I k') f.left
      (deformationSpecialFibreMap f hJ k').left where
  total := deformationTotalMap f hJ k'
  generic := deformationGenericMap f hJ k'
  comm_j := deformationGenericMap_toTotal f hJ k'
  comm_i := deformationSpecialFibreMap_toTotal f hJ k'
  comm_ε := by
    rw [deformationModel_ε, deformationModel_ε, deformationGenericMap_toTotal_assoc,
      deformationTotalMap_toBase, Category.assoc]

@[simp]
lemma deformationModelHom_total :
    (deformationModelHom f hJ k').total = deformationTotalMap f hJ k' :=
  rfl

@[simp]
lemma deformationModelHom_generic :
    (deformationModelHom f hJ k').generic = deformationGenericMap f hJ k' :=
  rfl

end Map

/-! ### The vertex of the tangent cone at a rational point -/

section Vertex

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- A rational point `x` of `X` factors uniquely through the closed subscheme `V(ker x)`. -/
lemma existsUnique_quotientSpecLift :
    ∃! h : (point k).left ⟶ x.left.ker.quotientSpec,
      h ≫ (relativeGluingData x.left.ker.coequifibered_toQuotientAlgebra).toBase = x.left :=
  (Scheme.Hom.ker_le_ker_iff_existsUnique_fac x.left _).mp
    (by rw [IdealSheafData.ker_quotientSpec_toBase])

/-- A rational point `x` of `X` factors through the closed subscheme `V(I)`, `I = ker x`. -/
noncomputable def quotientSpecLift : (point k).left ⟶ x.left.ker.quotientSpec :=
  (existsUnique_quotientSpecLift x).exists.choose

@[reassoc (attr := simp)]
lemma quotientSpecLift_toBase :
    quotientSpecLift x ≫ (relativeGluingData x.left.ker.coequifibered_toQuotientAlgebra).toBase =
      x.left :=
  (existsUnique_quotientSpecLift x).exists.choose_spec

/-- The vertex of the tangent cone at a rational point `x`, as a point `Spec k ⟶ D_I X` of the
deformation space (`I = ker x`): the point `x` of the zero section of the normal cone. -/
noncomputable def deformationSpaceVertex : (point k).left ⟶ x.left.ker.deformationSpace :=
  quotientSpecLift x ≫ x.left.ker.normalConeZeroSection ≫ x.left.ker.normalConeToDeformationSpace

/-- The vertex lies over the origin of `𝔸¹_k`. -/
lemma deformationSpaceVertex_deformationSpaceToAffineLine :
    deformationSpaceVertex x ≫ deformationSpaceToAffineLine X x.left.ker =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)) := by
  have h₁ := x.left.ker.isPullback_normalConeToDeformationSpace.w
  have h₂ : x.left.ker.normalConeToPolynomialZeroSpec ≫
      (relativeGluingData X.left.coequifibered_toPolynomialZeroPresheaf).toBase =
      (relativeGluingData x.left.ker.coequifibered_toNormalConePresheaf).toBase :=
    relativeGluingMap_toBase _ _ _
      x.left.ker.toPolynomialZeroPresheaf_comp_polynomialZeroToNormalCone
  have hx : x.left ≫ X.hom = 𝟙 _ := Over.w x
  rw [deformationSpaceVertex, deformationSpaceToAffineLine, Category.assoc, Category.assoc,
    reassoc_of% h₁, reassoc_of% polynomialZeroSpecToPolynomialSpec_comp_polynomialSpecToAffineSpace,
    reassoc_of% h₂, IdealSheafData.normalConeZeroSection_toBase_assoc,
    quotientSpecLift_toBase_assoc, AffineSpace.zeroSection_comp_map, reassoc_of% hx]

/-- The vertex of the tangent cone at a rational point `x` of `X`, as a `k'`-point of the special
fibre of the deformation to the normal cone of `x` over `Spec k'⟦t⟧`. -/
noncomputable def deformationVertex : point k' ⟶ deformationSpecialFibre X x.left.ker k' :=
  Over.homMk (pullback.lift (pullback.lift
      (Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ deformationSpaceVertex x)
      (traitClosedPoint k') (by
        rw [Category.assoc, deformationSpaceVertex_deformationSpaceToAffineLine,
          traitClosedPoint_traitToAffineLine]))
    (𝟙 _) (by rw [Category.id_comp]; exact pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma deformationVertex_toTotal :
    (deformationVertex x k').left ≫ deformationSpecialToTotal X x.left.ker k' =
      pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ deformationSpaceVertex x)
        (traitClosedPoint k') (by
          rw [Category.assoc, deformationSpaceVertex_deformationSpaceToAffineLine,
            traitClosedPoint_traitToAffineLine]) :=
  pullback.lift_fst _ _ _

/-- The vertex maps to the vertex of the tangent cone in the deformation space. -/
@[reassoc (attr := simp)]
lemma deformationVertex_toSpace :
    (deformationVertex x k').left ≫ deformationSpecialToTotal X x.left.ker k' ≫
        deformationTotalToSpace X x.left.ker k' =
      Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ deformationSpaceVertex x := by
  rw [deformationVertex_toTotal_assoc]
  exact pullback.lift_fst _ _ _

end Vertex

end AlgebraicGeometry.ProEtale.CondensedRing
