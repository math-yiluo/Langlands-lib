/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence

/-!

# The zero-section map of a rational point

Let `x` be a rational point of a `k`-scheme `X`, with ideal `I = ker x` and centre
`Z = V(I) ≅ Spec k`. The pullback exchange of the section `ẽ : S ⟶ 𝒳` of the deformation to the
normal cone of `x` (`ProEtale.CondensedRing.zeroSectionModelHom`) is the special case `Z = {x}` of
the zero-section map `ε_{X,Z}` of blueprint `prose-E-04`
(`ProEtale.CondensedRing.zeroSectionMap`): the constant family `Z × S` of the centre is isomorphic
to the trait `S` as a model, by the deformation `D_⊥ Z ≅ 𝔸¹_Z ≅ 𝔸¹_k` of the zero ideal of `Z`
(`ProEtale.CondensedRing.centreModelHom`), and `ẽ` factors through this isomorphism.

## Main results

- `ProEtale.CondensedRing.isIso_pullbackExchange_zeroSectionModelHom_app_of_isIso_zeroSectionMap`:
  if the zero-section map `ε_{X,Z}(K)` of the centre `Z = V(ker x)` is an isomorphism, then so is
  the pullback exchange of `ẽ` at `K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

/-! ### The constant family of the centre of a rational point -/

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The rational point `x`, as a point of the centre `Z = V(ker x)`. -/
noncomputable def centrePoint : (point k).left ⟶ (centre X x.left.ker).left :=
  x.left.toImage

@[reassoc (attr := simp)]
lemma centrePoint_centreι : centrePoint X x ≫ (centreι X x.left.ker).left = x.left :=
  x.left.toImage_imageι

instance : IsIso (centrePoint X x) := by
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  exact inferInstanceAs (IsIso x.left.toImage)

@[reassoc (attr := simp)]
lemma centrePoint_hom : centrePoint X x ≫ (centre X x.left.ker).hom = 𝟙 _ := by
  rw [← Over.w (centreι X x.left.ker), centrePoint_centreι_assoc]
  exact Over.w x

instance : IsIso (centre X x.left.ker).hom := by
  have : IsIso (centrePoint X x ≫ (centre X x.left.ker).hom) := by
    rw [centrePoint_hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (centrePoint X x) _

/-- The deformation space of the zero ideal of the centre `Z = V(ker x) ≅ Spec k` is the affine
line `𝔸¹_k`. -/
instance : IsIso (deformationSpaceToAffineLine (centre X x.left.ker) ⊥) := by
  unfold deformationSpaceToAffineLine
  infer_instance

/-- The section `𝔸¹_k ≅ 𝔸¹_Z ⟶ Spec_Z (𝒪_Z / ⊥)[t]` of the relative affine line of the zero ideal
of the centre. -/
noncomputable def centreQuotientPolynomialSection :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶
      (⊥ : (centre X x.left.ker).left.IdealSheafData).quotientPolynomialSpec :=
  AffineSpace.map _ (centrePoint X x) ≫ inv (centre X x.left.ker).left.polynomialSpecToAffineSpace ≫
    inv (relativeGluingMap (centre X x.left.ker).left.coequifibered_toPolynomialPresheaf
      (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : (centre X x.left.ker).left.IdealSheafData).polynomialToQuotientPolynomial)

/-- The section `𝔸¹_k ⟶ D_⊥ Z` of the deformation space of the zero ideal of the centre. -/
noncomputable def centreDeformationSection :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶
      (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpace :=
  centreQuotientPolynomialSection X x ≫
    relativeGluingMap (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toReesPresheaf
      (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : (centre X x.left.ker).left.IdealSheafData).reesToQuotientPolynomial

@[reassoc]
lemma centreDeformationSection_toPolynomialSpec :
    centreDeformationSection X x ≫
        (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpaceToPolynomialSpec =
      AffineSpace.map _ (centrePoint X x) ≫
        inv (centre X x.left.ker).left.polynomialSpecToAffineSpace := by
  rw [centreDeformationSection, IdealSheafData.deformationSpaceToPolynomialSpec, Category.assoc,
    ← relativeGluingMap_comp, IdealSheafData.polynomialToRees_comp_reesToQuotientPolynomial,
    centreQuotientPolynomialSection, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

@[reassoc (attr := simp)]
lemma centreDeformationSection_toAffineLine :
    centreDeformationSection X x ≫ deformationSpaceToAffineLine (centre X x.left.ker) ⊥ = 𝟙 _ := by
  rw [deformationSpaceToAffineLine, centreDeformationSection_toPolynomialSpec_assoc,
    IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp, centrePoint_hom]
  exact AffineSpace.map_id _

@[reassoc (attr := simp)]
lemma centreDeformationSection_toBase :
    centreDeformationSection X x ≫
        (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpaceProj =
      (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) ≫ centrePoint X x := by
  rw [IdealSheafData.deformationSpaceProj, ← relativeGluingMap_toBase
    (centre X x.left.ker).left.coequifibered_toPolynomialPresheaf
    (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toReesPresheaf _
    (⊥ : (centre X x.left.ker).left.IdealSheafData).toPolynomialPresheaf_comp_polynomialToRees,
    ← IdealSheafData.deformationSpaceToPolynomialSpec,
    centreDeformationSection_toPolynomialSpec_assoc,
    ← AffineSpace.map_over]
  congr 1
  rw [IsIso.inv_comp_eq]
  exact (polynomialSpecToAffineSpace_over _).symm

/-- The section `𝔸¹_k ⟶ D_⊥ Z` maps to the section `𝔸¹_k ⟶ D_x X` given by `x`. -/
@[reassoc]
lemma centreDeformationSection_deformationSpaceMap :
    centreDeformationSection X x ≫ IdealSheafData.deformationSpaceMap (centreι X x.left.ker).left
        x.left.ker ⊥ (siteIdeal_map_appLE_le_bot X x.left.ker) =
      x.left.deformationSpaceSection := by
  have hR : (IdealSheafData.quotientPolynomialPullbackData (centreι X x.left.ker).left x.left.ker ⊥
        (siteIdeal_map_appLE_le_bot X x.left.ker)).comparison
        x.left.ker.coequifibered_toQuotientPolynomialAlgebra
        (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra ≫
      relativeGluingMap x.left.ker.coequifibered_toReesPresheaf
        x.left.ker.coequifibered_toQuotientPolynomialAlgebra x.left.ker.reesToQuotientPolynomial =
      relativeGluingMap (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toReesPresheaf
        (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
        (⊥ : (centre X x.left.ker).left.IdealSheafData).reesToQuotientPolynomial ≫
        IdealSheafData.deformationSpaceMap (centreι X x.left.ker).left x.left.ker ⊥
          (siteIdeal_map_appLE_le_bot X x.left.ker) :=
    PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
      (IdealSheafData.reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map _ _ _ _)
  have hP : (IdealSheafData.quotientPolynomialPullbackData (centreι X x.left.ker).left x.left.ker ⊥
        (siteIdeal_map_appLE_le_bot X x.left.ker)).comparison
        x.left.ker.coequifibered_toQuotientPolynomialAlgebra
        (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra ≫
      relativeGluingMap X.left.coequifibered_toPolynomialPresheaf
        x.left.ker.coequifibered_toQuotientPolynomialAlgebra
        x.left.ker.polynomialToQuotientPolynomial =
      relativeGluingMap (centre X x.left.ker).left.coequifibered_toPolynomialPresheaf
        (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
        (⊥ : (centre X x.left.ker).left.IdealSheafData).polynomialToQuotientPolynomial ≫
        polynomialSpecMap (centreι X x.left.ker).left :=
    PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
      (IdealSheafData.polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
        _ _ _ _)
  rw [centreDeformationSection, Category.assoc, ← hR, Scheme.Hom.deformationSpaceSection,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono (relativeGluingMap X.left.coequifibered_toPolynomialPresheaf
      x.left.ker.coequifibered_toQuotientPolynomialAlgebra
      x.left.ker.polynomialToQuotientPolynomial), Category.assoc, hP,
    Scheme.Hom.affineSpaceToQuotientPolynomialSpec_toPolynomialSpec,
    centreQuotientPolynomialSection, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc,
    (IsIso.eq_comp_inv _).mpr (polynomialSpecMap_polynomialSpecToAffineSpace _), Category.assoc,
    IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp_assoc, centrePoint_centreι]

/-- The section `S ⟶ D_⊥ Z ×_{𝔸¹_k} S` of the total space of the constant family of the centre
`Z = V(ker x)`. -/
noncomputable def centreTotalSection : trait k' ⟶ deformationTotal (centre X x.left.ker) ⊥ k' :=
  pullback.lift (traitToAffineLine k k' ≫ centreDeformationSection X x) (𝟙 _) (by
    rw [Category.assoc, centreDeformationSection_toAffineLine, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma centreTotalSection_toSpace :
    centreTotalSection X x k' ≫ deformationTotalToSpace (centre X x.left.ker) ⊥ k' =
      traitToAffineLine k k' ≫ centreDeformationSection X x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma centreTotalSection_toTrait :
    centreTotalSection X x k' ≫ deformationTotalToTrait (centre X x.left.ker) ⊥ k' = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The total space of the constant family of the centre `Z ≅ Spec k` is the trait. -/
instance : IsIso (deformationTotalToTrait (centre X x.left.ker) ⊥ k') :=
  inferInstanceAs (IsIso (pullback.snd _ _))

instance : IsIso (centreTotalSection X x k') := by
  have : IsIso (centreTotalSection X x k' ≫
      deformationTotalToTrait (centre X x.left.ker) ⊥ k') := by
    rw [centreTotalSection_toTrait]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (deformationTotalToTrait (centre X x.left.ker) ⊥ k')

@[reassoc (attr := simp)]
lemma centreTotalSection_toBase :
    centreTotalSection X x k' ≫ deformationTotalToBase (centre X x.left.ker) ⊥ k' =
      traitToBase k k' ≫ centrePoint X x := by
  rw [deformationTotalToBase, centreTotalSection_toSpace_assoc,
    centreDeformationSection_toBase, traitToAffineLine_over_assoc]

/-- The section `ẽ : S ⟶ 𝒳` of the deformation to the normal cone of `x` factors through the
constant family of the centre. -/
@[reassoc (attr := simp)]
lemma centreTotalSection_deformationTotalMap :
    centreTotalSection X x k' ≫ deformationTotalMap (centreι X x.left.ker)
        (siteIdeal_map_appLE_le_bot X x.left.ker) k' =
      deformationZeroSectionTotal X x k' := by
  refine (isPullback_deformationTotal X x.left.ker k').hom_ext ?_ ?_
  · rw [Category.assoc, deformationTotalMap_toSpace, centreTotalSection_toSpace_assoc,
      centreDeformationSection_deformationSpaceMap,
      deformationZeroSectionTotal_toSpace]
  · rw [Category.assoc, deformationTotalMap_toTrait, centreTotalSection_toTrait,
      deformationZeroSectionTotal_toTrait]

/-- The geometric generic fibre `Spec Ω ⟶ D_⊥ Z ×_{𝔸¹_k} Spec Ω` of the section
`centreTotalSection`. -/
noncomputable def centreGenericSection :
    Spec (.of (traitGenericField k')) ⟶ deformationGeneric (centre X x.left.ker) ⊥ k' :=
  pullback.lift (traitGenericPoint k' ≫ centreTotalSection X x k') (𝟙 _) (by
    rw [Category.assoc, centreTotalSection_toTrait, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma centreGenericSection_toTotal :
    centreGenericSection X x k' ≫ deformationGenericToTotal (centre X x.left.ker) ⊥ k' =
      traitGenericPoint k' ≫ centreTotalSection X x k' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma centreGenericSection_snd :
    centreGenericSection X x k' ≫
      pullback.snd (deformationTotalToTrait (centre X x.left.ker) ⊥ k') (traitGenericPoint k') =
        𝟙 _ :=
  pullback.lift_snd _ _ _

instance : IsIso (centreGenericSection X x k') := by
  have : IsIso (centreGenericSection X x k' ≫
      pullback.snd (deformationTotalToTrait (centre X x.left.ker) ⊥ k')
        (traitGenericPoint k')) := by
    rw [centreGenericSection_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (pullback.snd (deformationTotalToTrait (centre X x.left.ker) ⊥ k') (traitGenericPoint k'))

/-- The geometric generic fibre of `ẽ` factors through the constant family of the centre. -/
lemma centreGenericSection_deformationGenericMap :
    centreGenericSection X x k' ≫ deformationGenericMap (centreι X x.left.ker)
        (siteIdeal_map_appLE_le_bot X x.left.ker) k' =
      deformationZeroSectionGeneric X x k' := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (centreGenericSection X x k' ≫ ·)
      (deformationGenericMap_toTotal (centreι X x.left.ker)
        (siteIdeal_map_appLE_le_bot X x.left.ker)
        k')).trans ((centreGenericSection_toTotal_assoc X x k' _).trans
      ((congrArg (traitGenericPoint k' ≫ ·) (centreTotalSection_deformationTotalMap X x k')).trans
        (deformationZeroSectionGeneric_toTotal X x k').symm)))
  · simp [deformationGenericMap, centreGenericSection, deformationZeroSectionGeneric]

/-- The special fibre `Z₀ ⟶ (D_⊥ Z ×_{𝔸¹_k} S)_s` of the section `centreTotalSection`. -/
noncomputable def centreSpecialFibreSection :
    (deformationSpecialZeroLocus X x.left.ker k').left ⟶
      (deformationSpecialFibre (centre X x.left.ker) ⊥ k').left :=
  pullback.lift (((deformationSpecialZeroLocus X x.left.ker k').hom ≫ traitClosedPoint k') ≫
    centreTotalSection X x k') (deformationSpecialZeroLocus X x.left.ker k').hom (by
      simp only [Category.assoc, centreTotalSection_toTrait, Category.comp_id])

@[reassoc (attr := simp)]
lemma centreSpecialFibreSection_toTotal :
    centreSpecialFibreSection X x k' ≫ deformationSpecialToTotal (centre X x.left.ker) ⊥ k' =
      ((deformationSpecialZeroLocus X x.left.ker k').hom ≫ traitClosedPoint k') ≫
        centreTotalSection X x k' :=
  pullback.lift_fst _ _ _

/-- The zero section `e` of the special fibre factors through the special fibre of the constant
family of the centre. -/
lemma centreSpecialFibreSection_zeroSectionSpecialFibreMap :
    centreSpecialFibreSection X x k' ≫ (zeroSectionSpecialFibreMap X x.left.ker k').left =
      (deformationSpecialFibreZeroSection X x.left.ker k').left := by
  refine (isPullback_deformationSpecialFibre X x.left.ker k').hom_ext ?_ ?_
  · rw [Category.assoc, zeroSectionSpecialFibreMap, deformationSpecialFibreMap_toTotal,
      centreSpecialFibreSection_toTotal_assoc,
      centreTotalSection_deformationTotalMap, deformationSpecialFibreZeroSection_toTotal,
      Category.assoc]
  · rw [Category.assoc, Over.w (zeroSectionSpecialFibreMap X x.left.ker k'),
      Over.w (deformationSpecialFibreZeroSection X x.left.ker k')]
    exact pullback.lift_snd _ _ _

/-- The isomorphism of models from the trait `S`, as the constant family of the point `Spec k`, to
the constant family `D_⊥ Z ×_{𝔸¹_k} S` of the centre `Z = V(ker x) ≅ Spec k`, over the point
`Spec k ≅ Z` given by `x`. -/
noncomputable def centreModelHom :
    (zeroSectionModel X k' x.left.ker).Hom (deformationModel (centre X x.left.ker) ⊥ k')
      (centrePoint X x) (centreSpecialFibreSection X x k') where
  total := centreTotalSection X x k'
  generic := centreGenericSection X x k'
  comm_j := centreGenericSection_toTotal X x k'
  comm_i := centreSpecialFibreSection_toTotal X x k'
  comm_ε := by
    rw [deformationModel_ε, centreGenericSection_toTotal_assoc, centreTotalSection_toBase]
    exact (Category.assoc _ _ _).symm

/-! ### The zero-section map of a rational point -/

/-- **The zero-section map of a rational point** (blueprint `prose-E-04`, the case
`Z = {x}`): if the zero-section map `ε_{X,Z}(K)` of the centre `Z = V(ker x)` is an isomorphism,
then so is the pullback exchange `Le^* Ψ_𝒳(K) ⟶ Ψ_S(Lx^* K)` of the section `ẽ : S ⟶ 𝒳` of the
deformation to the normal cone of `x`. The morphism of models `ẽ` factors as the isomorphism of
models `S ≅ D_⊥ Z ×_{𝔸¹_k} S` followed by the morphism of models defining `ε_{X,Z}`, and the
pullback exchanges compose along this factorization
(`NearbyCyclesModel.Hom.pullbackExchange_square`). -/
theorem isIso_pullbackExchange_zeroSectionModelHom_app_of_isIso_zeroSectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    [IsIso (zeroSectionMap X x.left.ker k' Λ K)] :
    IsIso (((zeroSectionModelHom X x k').pullbackExchange Λ).app K) := by
  have : IsIso ((centreModelHom X x k').pullbackExchange Λ) := by
    have : IsIso (centreModelHom X x k').total :=
      inferInstanceAs (IsIso (centreTotalSection X x k'))
    have : IsIso (centreModelHom X x k').generic :=
      inferInstanceAs (IsIso (centreGenericSection X x k'))
    exact (centreModelHom X x k').isIso_pullbackExchange_of_isIso Λ
  have : IsIso ((NearbyCyclesModel.Hom.id (deformationModel X x.left.ker k')).pullbackExchange
      Λ) := by
    have : IsIso (NearbyCyclesModel.Hom.id (deformationModel X x.left.ker k')).total :=
      inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (NearbyCyclesModel.Hom.id (deformationModel X x.left.ker k')).generic :=
      inferInstanceAs (IsIso (𝟙 _))
    exact (NearbyCyclesModel.Hom.id _).isIso_pullbackExchange_of_isIso Λ
  have : IsIso (((zeroSectionDeformationModelHom X x.left.ker k').pullbackExchange Λ).app K) :=
    ‹IsIso (zeroSectionMap X x.left.ker k' Λ K)›
  have h := NearbyCyclesModel.Hom.pullbackExchange_square Λ (zeroSectionModelHom X x k')
    (NearbyCyclesModel.Hom.id _) (centreModelHom X x k')
    (zeroSectionDeformationModelHom X x.left.ker k')
    ((Category.comp_id _).trans (centreTotalSection_deformationTotalMap X x k').symm)
    ((Category.comp_id _).trans (centreGenericSection_deformationGenericMap X x k').symm)
    ((Category.comp_id _).trans (centrePoint_centreι X x).symm)
    ((Category.comp_id _).trans (centreSpecialFibreSection_zeroSectionSpecialFibreMap X x k').symm)
    K
  have := IsIso.of_isIso_fac_left h
  have : IsIso (((zeroSectionModelHom X x k').pullbackExchange Λ).app
      (L((𝟙 X.left)^*⟦Λ⟧).obj K)) :=
    IsIso.of_isIso_comp_left
      (L(((deformationSpecialFibreZeroSection X x.left.ker k').left)^*⟦Λ⟧).map
        (((NearbyCyclesModel.Hom.id (deformationModel X x.left.ker k')).pullbackExchange Λ).app
          K)) _
  have e : K ≅ L((𝟙 X.left)^*⟦Λ⟧).obj K := ((leftDerivedUpperStarId Λ X.left).app K).symm
  have hn := ((zeroSectionModelHom X x k').pullbackExchange Λ).naturality e.hom
  exact IsIso.of_isIso_fac_right hn.symm

end AlgebraicGeometry.ProEtale.CondensedRing
