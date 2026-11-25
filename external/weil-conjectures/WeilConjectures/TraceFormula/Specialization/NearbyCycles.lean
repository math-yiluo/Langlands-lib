/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.SpecialFibre
public import WeilConjectures.TraceFormula.Specialization.DeformationModelFactor
public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.NearbyKunneth
public import WeilConjectures.TraceFormula.Specialization.ZeroSectionPoint
public import WeilConjectures.TraceFormula.Specialization.ZeroSectionVanishing

/-!

# Nearby cycles of the deformation of a contracting correspondence

Let `c = (c₁, c₂) : C ⟶ X × X` be contracting at the `k`-point `y` of its support, with
`x = c₁(y) = c₂(y)`, and let `k'` be a separably closed extension of `k`. The deformations to the
normal cones of `x ∈ X` and `y ∈ C`, base changed to the strictly henselian trait `Spec k'⟦t⟧`, are
models of `X` and `C` of finite type over the trait; so are the product model of `X × X` and the
model of the fixed locus. Their nearby cycles `Ψ = i^* Rj_* ε^*` restrict to the bounded
constructible derived categories by Deligne's finiteness theorem
(`ProEtale.CondensedRing.NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`).

This file defines
* the specialization functors `Ψ_X`, `Ψ_C`, `Ψ_{X×X}`, `Ψ_F`
  (`ProEtale.CondensedRing.specialization`, `ProEtale.CondensedRing.specializationProd`,
  `ProEtale.CondensedRing.Correspondence.IsContractingAt.specializationFixedLocus`);
* the *specialized correspondence* `c' = (γ₁, γ₂) : N_y C ⊗ k' ⟶ N_x X ⊗ k'` of
  `(N_x X ⊗ k', Ψ_X K)`
  (`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialCorrespondence`) and its fixed
  locus
  (`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialFixedLocus`);

and states the two theorems on nearby cycles that Varshavsky's vanishing argument uses:
* Gabber's Künneth formula and the commutation of nearby cycles with Verdier duality, in the form
  `Ψ_{X×X}(K ⊠ D K) ≅ Ψ_X K ⊠ D Ψ_X K`
  (`ProEtale.CondensedRing.nonempty_specializationProd_externalProduct_iso`, proved downstream
  once the dualizing maps of nearby cycles are constructed);
* Verdier's zero-section theorem: the specialization `Sp_{X,x}(K) = Ψ_X K` restricted to the zero
  section vanishes if `K_x` does
  (`ProEtale.CondensedRing.isZero_upperStar_zeroSection_specialization`). It is deduced from its
  exchange form: the pullback exchange along the section `ẽ : S ⟶ 𝒳` of the deformation to the
  normal cone is invertible
  (`ProEtale.CondensedRing.isIso_pullbackExchange_zeroSectionModelHom_app`), the case `Z = {x}` of
  the invertibility of the zero-section map for all closed subschemes
  (`ProEtale.CondensedRing.isIso_zeroSectionMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section ZeroSection

variable (k') (x : RationalPoint X)

/-- The *specialization* `Sp_{X,x} : Dᵇc(X) ⥤ Dᵇc(N_x X ⊗ k')` to the normal cone of a rational
point `x` (Verdier, *Spécialisation de faisceaux et monodromie modérée*): the nearby cycles of the
deformation to the normal cone of `x`, base changed to the trait `Spec k'⟦t⟧`. -/
noncomputable def specialization :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((deformationSpecialFibre X x.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))

/-- **Verdier's zero-section theorem, exchange form** (Verdier, *Spécialisation de faisceaux et
monodromie modérée*, Prop. 8.(5); blueprint `theorem-verdier-s-theorem-specialization-zero--1`, for
the closed subscheme `Z = x`, with the constant family identification of
`lemma-nearby-cycles-constant-family`): for `K` bounded constructible on `X`, the pullback exchange
`α : Le^* Sp_{X,x}(K) ⟶ Ψ_S(Lx^* K)` along the section `ẽ : S ⟶ 𝒳` of the deformation to the
normal cone (`ProEtale.CondensedRing.zeroSectionModelHom`) is an isomorphism. Followed by the
inverse of the (invertible) specialization unit of the constant family `S`, it is the zero-section
map `ε_{X,x}(K) : e^* Sp_{X,x}(K) ⟶ x^* K` of blueprint `prose-E-04`, which the
blueprint node asserts to be an isomorphism. The section `ẽ` is a closed immersion, so the smooth
pullback exchange of blueprint `prose-E-03` does not apply to it; instead this
is the case `I = ker x` of `ProEtale.CondensedRing.isIso_zeroSectionMap`, transported along
`ProEtale.CondensedRing.isIso_pullbackExchange_zeroSectionModelHom_app_of_isIso_zeroSectionMap`. -/
theorem isIso_pullbackExchange_zeroSectionModelHom_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (((zeroSectionModelHom X x k').pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
      K.obj) := by
  have h : IsIso (zeroSectionMap X x.left.ker k' (Profinite.padicAlgClRingObj ℓ) K.obj) :=
    isIso_zeroSectionMap (ℓ := ℓ) k' X x.left.ker K
  have h₁ := @isIso_pullbackExchange_zeroSectionModelHom_app_of_isIso_zeroSectionMap _ _ X x k'
    _ _ (Profinite.padicAlgClRingObj ℓ) _ _
  have h₂ := h₁ K.obj
  exact h₂

/-- **Verdier's zero-section theorem** (Verdier, *Spécialisation de faisceaux et monodromie
modérée*, Prop. 8.(5); blueprint `theorem-verdier-s-theorem-specialization-zero--1`,
`theorem-verdier-s-theorem-specialization-zero`): the restriction of the specialization
`Sp_{X,x}(K)` to the zero section `x ⊗ k'` of the normal cone is the base change of the stalk `K_x`;
in particular it vanishes if `K_x` does. -/
theorem isZero_upperStar_zeroSection_specialization
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (deformationSpecialFibreZeroSection X x.left.ker k')).obj
        ((specialization k' x).obj K)) := by
  have := isIso_pullbackExchange_zeroSectionModelHom_app (ℓ := ℓ) k' x K
  have h₁ : IsZero ((L((x.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) :=
    ((boundedConstructible _).ι.map_isZero hK).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ x).app K).symm
  have h₃ := (zeroSectionModelHom X x k').isZero_upperStar_nearbyCycles_obj _ h₁
  exact IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
    (h₃.of_iso ((boundedConstructibleUpperStarCompatibility _ ℓ
      (deformationSpecialFibreZeroSection X x.left.ker k')).app ((specialization k' x).obj K)))

/-- The specialization `Dᵇc(X × X) ⥤ Dᵇc((N_x X ⊗ k') × (N_x X ⊗ k'))` of the product: the nearby
cycles of the product over the trait of two copies of the deformation to the normal cone of
`x`. -/
noncomputable def specializationProd :
    Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((deformationSpecialFibre X x.left.ker k' ⨯
        deformationSpecialFibre X x.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))

private lemma isIso_homMk_aux {C : Type*} [Category* C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (f : A.obj ⟶ B.obj) [hf : IsIso f] : IsIso (P.homMk f) :=
  haveI : IsIso (P.ι.map (P.homMk f)) := hf
  isIso_of_fully_faithful P.ι _

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k).Prime] in
/-- The product of two deformation models is their product over the trait, with the projections
`deformationProdFstModelHom` and `deformationProdSndModelHom`. -/
theorem isTraitProduct_deformationProdModel (I : X.left.IdealSheafData) :
    NearbyCyclesModel.IsTraitProduct (deformationProdFstModelHom X I X I k')
      (deformationProdSndModelHom X I X I k') where
  exists_isTraitModelOver :=
    ⟨deformationTotalToTrait X I k', pullback.snd _ _, deformationTotalToTrait X I k',
      pullback.snd _ _,
      ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
        isPullback_deformationSpecialFibre X I k'⟩,
      ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
        isPullback_deformationSpecialFibre X I k'⟩,
      IsPullback.of_hasPullback _ _,
      ⟨inferInstanceAs (LocallyOfFiniteType (deformationProdTotalToTrait X I X I k')),
        inferInstanceAs (QuasiCompact (deformationProdTotalToTrait X I X I k')),
        inferInstanceAs (IsSeparated (deformationProdTotalToTrait X I X I k')),
        by
          change IsPullback _ (deformationProdFstGeneric X I X I k' ≫ pullback.snd _ _)
            (deformationProdTotalToTrait X I X I k') _
          rw [deformationProdFstGeneric, pullback.lift_snd, Category.comp_id]
          exact IsPullback.of_hasPullback _ _,
        isPullback_deformationProdSpecialToTotal X I X I k'⟩,
      by simp [deformationProdSndModelHom, deformationProdFstModelHom, deformationProdFstGeneric,
        deformationProdSndGeneric]⟩
  exists_comp_ε_left := deformationModel_exists_comp_ε X I k'
  exists_comp_ε_right := deformationModel_exists_comp_ε X I k'

/-- The Künneth map `Π_{K,L} : Sp_{X,x} K ⊠ Sp_{X,x} L ⟶ Sp_{X × X,(x,x)} (K ⊠ L)` of the
specialization (blueprint `proposition-external-kunneth-formula-nearby-cycles`): the Künneth map of
nearby cycles `NearbyCyclesModel.kunnethMap` of the projections of the product of the deformation
models. -/
noncomputable def specializationKunnethMap (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ ((specialization k' x).obj K) ((specialization k' x).obj L) ⟶
      (specializationProd k' x).obj (externalProduct ℓ K L) :=
  ObjectProperty.homMk (NearbyCyclesModel.kunnethMap (Profinite.padicAlgClRingObj ℓ)
    (deformationProdFstModelHom X x.left.ker X x.left.ker k')
    (deformationProdSndModelHom X x.left.ker X x.left.ker k') K.obj L.obj)

/-- **Gabber's Künneth formula for the specialization** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`):
`Π_{K,L} : Sp_{X,x} K ⊠ Sp_{X,x} L ⟶ Sp (K ⊠ L)` is an isomorphism, by
`NearbyCyclesModel.isIso_kunnethMap`. -/
instance isIso_specializationKunnethMap (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (specializationKunnethMap (ℓ := ℓ) k' x K L) := by
  have h := NearbyCyclesModel.isIso_kunnethMap ℓ
    (isTraitProduct_deformationProdModel k' x.left.ker) K.property L.property
  exact isIso_homMk_aux _

end ZeroSection

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y)

variable (k' c y) in
/-- The *specialized complex* `Ψ_X K = Sp_{X,x}(K)` on the normal cone `N_x X ⊗ k'` of
`x = c₁(y)`: the specialization of `K` at `x`, the complex of the specialized correspondence
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialCorrespondence`). -/
noncomputable def specialComplex :
    Dᵇc((deformationSpecialFibre X (y ≫ c.c₁).left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (specialization k' (y ≫ c.c₁)).obj K

namespace IsContractingAt

variable (k')

/-- The *specialized correspondence* `c' = (γ₁, γ₂) : N_y C ⊗ k' ⟶ N_x X ⊗ k'` of the
specialization `Ψ_X K` of `K` to the normal cone of `x = c₁(y)`: the special fibre of the
deformation of `c` to the normal cones (blueprint
`theorem-contracting-correspondences-local-terms`). Its coefficient map plays no role in the
vanishing argument and is taken to be zero. -/
noncomputable def specialCorrespondence :
    Correspondence ℓ (c.specialComplex k' y) where
  C := deformationSpecialFibre c.C y.left.ker k'
  c₁ := hc.specialLeg₁ k'
  c₂ := hc.specialLeg₂ k'
  u := 0

/-- The fixed locus of the specialized correspondence, the fibre product `C' ×_{X' × X'} X'`. -/
noncomputable def specialFixedLocus : (hc.specialCorrespondence k').FixedLocus where
  F := fixedLocusOfDiag (hc.specialLeg₁ k') (hc.specialLeg₂ k')
  ι := fixedLocusOfDiag.ι _ _
  w := fixedLocusOfDiag.w _ _
  isLimit := fixedLocusOfDiag.isLimit _ _

/-- The specialization `Ψ_F` of the fixed locus `F`: the nearby cycles of the fibre product over
the trait of the deformed support `𝒞 ⟶ 𝒳 ×_S 𝒳` with the diagonal of `𝒳`, whose special fibre is
the fixed locus of the specialized correspondence. -/
noncomputable def specializationFixedLocus (F : c.FixedLocus) :
    Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((hc.specialFixedLocus k').F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((deformationFixedLocusModel k' c.c₁ c.c₂ hc.ker_map_le_c₁ hc.ker_map_le_c₂
      F.isPullback).preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationFixedLocusModel k' c.c₁ c.c₂ _ _ F.isPullback)
      (deformationFixedLocusModel_exists_comp_ε k' c.c₁ c.c₂ _ _ F.isPullback))

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
