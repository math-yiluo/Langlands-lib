/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Induction
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.RadicialDescent
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.CategoryTheory.Abelian.AnnihilatorDevissage
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.SmoothGenericDirectImage
import WeilConjectures.ConstructibleSheaf.OfForget
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Deligne's generic constructibility for an open immersion

Let `S` be an integral scheme of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, let `j : X ⟶ Y` be an open immersion of finite-type `S`-schemes and
let `F` be a constructible sheaf of `Λ`-modules on `X_ét`. Deligne's generic constructibility
theorem (SGA 4½, [Th. finitude], Thm. 1.9) says that over a nonempty open `U ⊆ S` the direct
image `Rj_* F` is bounded constructible and its formation commutes with every base change
`T ⟶ U` from a noetherian scheme.

The property "over `U`, the direct image is bounded constructible and commutes with base
change" is `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`. It is phrased
through all cartesian squares over noetherian `T ⟶ S` with image in `U`: taking for `T` the open
subscheme `U` itself gives the bounded constructibility of `Rj_{U,*}(F|_{X_U})`, and the base
change map along `Y_T ⟶ Y` is the composite of the one along `Y_T ⟶ Y_U` with the base change
map along the open immersion `Y_U ⟶ Y`, which is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn`: Deligne's generic
  constructibility (`theorem-generic-constructibility-base-change-rj`).
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field`
  :
  over a field, `Rj_* F` is bounded constructible (`corollary-open-direct-image-over-field--1`).
- `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`:
  descent of the property along a finite, surjective, radicial base change
  (`lemma-universal-homeomorphism-base--1`).

## Implementation notes

The blueprint states the theorem and its corollary over a field for `𝔽_ℓ`-coefficients, and
obtains arbitrary finite coefficients `Λ` by a dévissage
(`corollary-open-direct-image-over-field--1`). Its
proof applies verbatim to any finite `Λ` whose exponent is invertible on `S`, and we state it in
that generality.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

private theorem finiteUnderlying
    {A : Type (u + 1)} [CommRing A] [Finite A] {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    [h : IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ z ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj
      (F.over _)).IsConstant _)
  · have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hfg := h.isFinitelyGenerated_sheafFiber Ω z
    rw [ModuleCat.isFinitelyGenerated_iff] at hfg
    have : Finite (((pointSmallEtale z).sheafFiber (A := ModuleCat.{u + 1} A)).obj F) :=
      Module.finite_of_finite A
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this (((pointSmallEtale z).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} A))).app F).symm.toEquiv

private theorem finiteLocal_of_abelianIso
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))
    (e : (moduleAbelianForget A Z).obj F ≅ (moduleAbelianForget B Z).obj G)
    [IsFiniteLocallyConstantSheaf F] : IsFiniteLocallyConstantSheaf G := by
  have hF := finiteUnderlying F
  let e' := (sheafCompose Z.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e
  apply IsFiniteLocallyConstantSheaf.of_forget
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hF
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ z ↦ ?_⟩⟩
  · obtain ⟨M, ⟨e0⟩⟩ := (h𝒰 i).mem_essImage
    exact Sheaf.isConstant_of_iso _
      (((Z.smallEtaleTopology.overPullback _ _).mapIso e').symm ≪≫ e0.symm)
  · exact (hfin.isFinitelyGenerated_sheafFiber Ω z).of_iso
      ((pointSmallEtale z).sheafFiber.mapIso e')

private theorem constructible_of_abelianIso
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))
    (e : (moduleAbelianForget A Z).obj F ≅ (moduleAbelianForget B Z).obj G)
    [IsConstructibleSheaf F] : IsConstructibleSheaf G := by
  obtain ⟨s, hs⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
    (CA := fun M : ModuleCat.{u + 1} A ↦ M) (F := F)
  refine ⟨s, fun i ↦ ?_⟩
  have := hs i
  apply finiteLocal_of_abelianIso ((upperStar (ModuleCat.{u + 1} A) (s.immersion i)).obj F)
  exact (moduleAbelianUpperStarIso A (s.immersion i)).symm.app F ≪≫
    (upperStar AddCommGrpCat.{u + 1} (s.immersion i)).mapIso e ≪≫
    (moduleAbelianUpperStarIso B (s.immersion i)).app G

private theorem zero_of_forget_zero
    {A : Type (u + 1)} [CommRing A] {Z : Scheme.{u}}
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h : IsZero ((moduleAbelianForget A Z).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply (moduleAbelianForget A Z).map_injective
  simpa using h

private theorem boundedConstructible_of_abelianIso
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    {Z : Scheme.{u}}
    (K : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (e : (moduleAbelianForget A Z).mapDerivedCategoryPlus.obj K ≅
      (moduleAbelianForget B Z).mapDerivedCategoryPlus.obj L)
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z K.obj) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) Z L.obj := by
  let eH (i : ℤ) :=
    ((moduleAbelianForget A Z).mapDerivedCategoryPlusHomologyFunctorIso i).app K ≪≫
    (_root_.DerivedCategory.Plus.homologyFunctor _ i).mapIso e ≪≫
    ((moduleAbelianForget B Z).mapDerivedCategoryPlusHomologyFunctorIso i).symm.app L
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2 fun i hi ↦ ?_⟩,
    ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2 fun i hi ↦ ?_⟩⟩, fun i ↦ ?_⟩
  · apply zero_of_forget_zero
    exact ((moduleAbelianForget A Z).map_isZero
      ((_root_.DerivedCategory.isGE_iff _ a).1 ha i hi)).of_iso (eH i).symm
  · apply zero_of_forget_zero
    exact ((moduleAbelianForget A Z).map_isZero
      ((_root_.DerivedCategory.isLE_iff _ b).1 hb i hi)).of_iso (eH i).symm
  · let : IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ i).obj K) := hc i
    exact constructible_of_abelianIso _ _ (eH i)

private theorem exchange_iso_iff_abelian
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj K)) := by
  have he := moduleAbelianDerivedExchange_compatibility A sq K
  have hforgot :
      IsIso ((moduleAbelianForget A Y').mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K)) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj K)) := by
    rw [← isIso_comp_right_iff _ (moduleAbelianDerivedExchangeTargetIso A g' f' K).hom,
      he, isIso_comp_left_iff]
  constructor
  · intro h
    exact hforgot.mp inferInstance
  · intro h
    have := hforgot.mpr h
    apply (_root_.DerivedCategory.Plus.isIso_iff _).mpr
    intro i
    have := Functor.map_isIso (_root_.DerivedCategory.Plus.homologyFunctor _ i)
      ((moduleAbelianForget A Y').mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K))
    have : IsIso ((moduleAbelianForget A Y').map
        ((_root_.DerivedCategory.Plus.homologyFunctor _ i).map
          ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K))) :=
      (NatIso.isIso_map_iff
        ((moduleAbelianForget A Y').mapDerivedCategoryPlusHomologyFunctorIso i)
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K)).2 this
    exact isIso_of_reflects_iso _ (moduleAbelianForget A Y')

private theorem property_of_abelianIso
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (e : (moduleAbelianForget A X).mapDerivedCategoryPlus.obj K ≅
      (moduleAbelianForget B X).mapDerivedCategoryPlus.obj L) (U : Set S)
    (hK : HasDirectImageBaseChangeOnPlus A fY j K U) :
    HasDirectImageBaseChangeOnPlus B fY j L U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨hc, hi⟩ := hK T t ht YT XT g fT g' jT hY sq
  let eT := moduleAbelianDerivedExchangeTargetIso A g' jT K ≪≫
    (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus ⋙
      (lowerStar AddCommGrpCat.{u + 1} jT).rightDerivedFunctorPlus).mapIso e) ≪≫
    (moduleAbelianDerivedExchangeTargetIso B g' jT L).symm
  refine ⟨boundedConstructible_of_abelianIso _ _ eT hc, ?_⟩
  apply (exchange_iso_iff_abelian B sq.toCommSq L).2
  exact (NatTrans.isIso_app_iff_of_iso _ e).1
    ((exchange_iso_iff_abelian A sq.toCommSq K).1 hi)

private theorem property_of_open
    (A : Type (u + 1)) [CommRing A] [Finite A] {S X : Scheme.{u}} (a : X ⟶ S)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (U : S.Opens)
    (hc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) U.toScheme
      (((a ∣_ U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlus.obj
        ((((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlus.obj K)).obj)
    (hi : ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
      (XT : Scheme.{u}) (vX : XT ⟶ (a ⁻¹ᵁ U).toScheme) (aT : XT ⟶ T)
      (sq : IsPullback vX aT (a ∣_ U) v),
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app
        ((((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlus.obj K))) :
    HasDirectImageBaseChangeOnPlus A (𝟙 S) a K U := by
  intro T _ t ht YT XT g fT g' aT hY sq
  have : IsIso fT := hY.isIso_snd_of_isIso
  have : IsLocallyNoetherian YT := LocallyOfFiniteType.isLocallyNoetherian fT
  have : CompactSpace YT := QuasiCompact.compactSpace_of_compactSpace fT
  have : IsNoetherian YT := {}
  have hg : Set.range g ⊆ Set.range U.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have he : g = fT ≫ t := by simpa using hY.w
    rw [he, Scheme.Hom.comp_apply]
    exact ht ⟨fT x, rfl⟩
  let v : YT ⟶ U := IsOpenImmersion.lift U.ι g hg
  have hv : v ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hR : IsPullback (a ⁻¹ᵁ U).ι (a ∣_ U) a U.ι :=
    (isPullback_morphismRestrict a U).flip
  let vX : XT ⟶ (a ⁻¹ᵁ U) := hR.lift g' (aT ≫ v) (by rw [Category.assoc, hv, sq.w])
  have hvX : vX ≫ (a ⁻¹ᵁ U).ι = g' := hR.lift_fst _ _ _
  have hs : IsPullback vX aT (a ∣_ U) v := by
    apply IsPullback.of_right _ _ hR
    · simpa only [hvX, hv] using sq
    · exact hR.lift_snd _ _ _
  have hleft := hi YT v XT vX aT hs
  have hright := isIso_derivedBaseChangeMapPlus_of_etale (Λ := A) hR
  let P := ((((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlus.obj K)
  let e := (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) vX (a ⁻¹ᵁ U).ι g'
    hvX.symm).app K
  refine ⟨?_, ?_⟩
  · have hb := hc.mapDerivedCategory_upperStar v
    let eb := asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) hs.toCommSq).app P)
    have hb' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) YT
        (((v)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlus.obj
          (((a ∣_ U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlus.obj P)).obj := hb
    exact ObjectProperty.prop_of_iso _
      (_root_.DerivedCategory.Plus.ι.mapIso
        (eb ≪≫ ((aT)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlus.mapIso e.symm)) hb'
  · have hp := (isIso_derivedBaseChangeMapPlus_app_paste_horiz_iff hR.toCommSq hs.toCommSq
      (hs.toCommSq.horiz_comp hR.toCommSq) K hleft).2 inferInstance
    exact (isIso_derivedBaseChangeMapPlus_app_congr hvX hv _ _ K).1 hp

private theorem property_of_shortExact
    {A : Type (u + 1)} [CommRing A] [Finite A] {S X : Scheme.{u}} (a : X ⟶ S)
    (E : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hE : E.ShortExact) (U : Set S)
    (h₁ : HasDirectImageBaseChangeOnPlus A (𝟙 S) a
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁) U)
    (h₃ : HasDirectImageBaseChangeOnPlus A (𝟙 S) a
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃) U) :
    HasDirectImageBaseChangeOnPlus A (𝟙 S) a
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂) U := by
  obtain ⟨δ, hδ⟩ := hE.exists_mk_singleTrianglePlus_distinguished
  apply HasDirectImageBaseChangeOnPlus.of_distTriang₂
    (Λ := A) (fY := 𝟙 S) (j := a) (U := U)
    (Tr := Pretriangulated.Triangle.mk
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map E.f)
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map E.g) δ)
    hδ h₁ h₃

private theorem smooth_prime_property
    {k : Type u} [Field k] {S X : Scheme.{u}} [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ ringChar k) (a : X ⟶ S)
    [Smooth a] [IsSeparated a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))))
    [IsFiniteLocallyConstantSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasDirectImageBaseChangeOnPlus (ULift.{u + 1} (ZMod p)) (𝟙 S) a
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  let A := ULift.{u + 1} (ZMod p)
  obtain ⟨U, hU, h⟩ := exists_nonempty_open_smooth_directImage_lisse_baseChange
    k S aS p hp X a F inferInstance
  have sqU : IsPullback (a ⁻¹ᵁ U).ι (a ∣_ U) a U.ι :=
    (isPullback_morphismRestrict a U).flip
  obtain ⟨hb, hl, hi⟩ := h (a ⁻¹ᵁ U) (a ⁻¹ᵁ U).ι (a ∣_ U) sqU
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let P := (((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlus.obj K
  let e : ((L(((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A])).obj K.obj) ≅ P.obj :=
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (a ⁻¹ᵁ U).ι).app K.obj
  have hc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) U.toScheme
      ((R((a ∣_ U)_*[ModuleCat.{u + 1} A])).obj
        ((L(((a ⁻¹ᵁ U).ι)^*[ModuleCat.{u + 1} A])).obj K.obj)) := by
    obtain ⟨l, r, _, hz⟩ := hb
    refine ⟨⟨⟨l, (_root_.DerivedCategory.isGE_iff _ l).2
      (fun i hi ↦ hz i (Or.inl hi))⟩,
      ⟨r, (_root_.DerivedCategory.isLE_iff _ r).2
        (fun i hi ↦ hz i (Or.inr hi))⟩⟩, fun i ↦ ?_⟩
    exact (hl i).isConstructibleSheaf
  refine ⟨U, ⟨hU.some.1, hU.some.2⟩, ?_⟩
  apply property_of_open A a K U
  · exact ObjectProperty.prop_of_iso _
      (((R((a ∣_ U)_*[ModuleCat.{u + 1} A])).mapIso e) ≪≫
        (((a ∣_ U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app P).symm) hc
  · intro T _ v XT vX aT sq
    have hu := hi T v XT vX aT sq
    have hp : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app P.obj) :=
      (NatTrans.isIso_app_iff_of_iso _ e).1 hu
    exact (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} A) sq.toCommSq P).1 hp

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- A smooth source with finite locally constant coefficients.
(blueprint: lem-fin-smooth-generic-direct-image-finite-ring)

For a separated smooth morphism of finite type `a : X ⟶ S` to an integral scheme of finite type
over a field on which the exponent of `Λ` is invertible, and a finite locally constant sheaf `F`
on `X`, there is a nonempty open `U ⊆ S` over which `Ra_* F` is bounded constructible and
commutes with every base change from a noetherian scheme
(`AlgebraicGeometry.Etale.SmoothGenericDirectImage`).

This records the form of the node used by the induction for
`theorem-generic-constructibility-base-change-rj`: the blueprint asks for `𝔽_ℓ`-coefficients and
finite locally constant cohomology sheaves of `Rf_{U,*} L`, whereas this states bounded
constructibility (with base change) over any finite ring `Λ` whose exponent is invertible on `S`. -/
theorem smoothGenericDirectImage : SmoothGenericDirectImage Λ := by
  intro k _ S X _ aS _ _ _ a _ _ _ F _
  obtain ⟨n, hn, hnΛ, hnu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  apply CategoryTheory.Abelian.prop_of_nsmul_id_eq_zero_of_isUnit (R := Γ(S, ⊤))
    (fun G ↦ IsFiniteLocallyConstantSheaf G)
    (fun G ↦ ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasDirectImageBaseChangeOnPlus Λ (𝟙 S) a
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) U)
    (fun G h p ↦ by
      have := h
      exact IsFiniteLocallyConstantSheaf.kernel (p • 𝟙 G))
    (fun G h p ↦ by
      have := h
      have := IsFiniteLocallyConstantSheaf.kernel (p • 𝟙 G)
      exact IsFiniteLocallyConstantSheaf.cokernel (kernel.ι (p • 𝟙 G)))
    (fun G hz ↦ ⟨⊤, by simp,
      HasDirectImageBaseChangeOnPlus.of_isZero
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map_isZero hz)⟩)
    (fun E hE h₁ h₃ ↦ by
      obtain ⟨U, hU, hUK⟩ := h₁
      obtain ⟨V, hV, hVQ⟩ := h₃
      refine ⟨U ⊓ V, nonempty_preirreducible_inter U.isOpen V.isOpen hU hV, ?_⟩
      exact property_of_shortExact a E hE (U ⊓ V : S.Opens)
        (hUK.mono (show ((U ⊓ V : S.Opens) : Set S) ⊆ U from inf_le_left))
        (hVQ.mono (show ((U ⊓ V : S.Opens) : Set S) ⊆ V from inf_le_right)))
    (fun p hp hpunit G hG hkill ↦ by
      have := hG
      have hpchar : p ≠ ringChar k := by
        intro heq
        have hz : (p : k) = 0 := by rw [heq, CharP.cast_eq_zero]
        have hzS : (p : Γ(S, ⊤)) = 0 := by
          rw [← map_natCast aS.appTop.hom,
            ← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, hz, map_zero, map_zero]
        rw [hzS] at hpunit
        obtain ⟨x⟩ := (inferInstance : Nonempty S)
        exact not_isUnit_zero (M₀ := S.presheaf.stalk x)
          (by simpa using hpunit.map (S.presheaf.germ ⊤ x trivial).hom)
      have : Fact p.Prime := ⟨hp⟩
      have hUK : p • 𝟙 ((moduleAbelianForget Λ X).obj G) = 0 := by
        have h := congrArg (moduleAbelianForget Λ X).map hkill
        rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
        exact h
      obtain ⟨H, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X p
        ((moduleAbelianForget Λ X).obj G) hUK
      have : IsFiniteLocallyConstantSheaf H := finiteLocal_of_abelianIso G H e.symm
      obtain ⟨U, hU, hUP⟩ := smooth_prime_property aS p hpchar a H
      let forgetH := moduleAbelianForget (ULift.{u + 1} (ZMod p)) X
      let eK := (forgetH.mapDerivedCategoryPlusSingleFunctor 0).app H ≪≫
        (_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso e ≪≫
        ((moduleAbelianForget Λ X).mapDerivedCategoryPlusSingleFunctor 0).symm.app G
      have hUK : HasDirectImageBaseChangeOnPlus Λ (𝟙 S) a
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) U :=
        property_of_abelianIso (𝟙 S) a _ _ eK U hUP
      exact ⟨U, hU, hUK⟩) n hn hnu F inferInstance
  ext V x
  change n • x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hnΛ, zero_smul]

/-- Blueprint `theorem-generic-constructibility-base-change-rj`: Generic bounded constructibility
for an open immersion.

Let `S` be integral and of finite type over a field `k`, let `Λ` be a finite ring whose exponent
is invertible on `S` (the blueprint takes `Λ = 𝔽_ℓ` with `ℓ ≠ char k`), and let `j : X ⟶ Y` be
an open immersion of finite-type `S`-schemes. For a constructible sheaf `F` of `Λ`-modules on
`X`, there is a nonempty open `U ⊆ S` such that `Rj_{U,*}(F|_{X_U})` is bounded constructible
and, for every morphism `T ⟶ U` with noetherian `T`, its base change morphism
`(Rj_{U,*} F|_{X_U})|_{Y_T} ⟶ Rj_{T,*}(F|_{X_T})` is an isomorphism; see
`AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn` for the formulation. -/
theorem exists_hasConstructibleDirectImageBaseChangeOn {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasConstructibleDirectImageBaseChangeOn Λ fY j F U :=
  exists_hasConstructibleDirectImageBaseChangeOn_of_smoothGenericDirectImage
    (Λ := Λ) (smoothGenericDirectImage Λ) aS fY j F

omit [Finite Λ] in
/-- Blueprint `lemma-universal-homeomorphism-base--1`: Descending the exchange property through a
universal homeomorphism.

Let `π : S' ⟶ S` be finite, surjective and radicial (universally injective), let `j : X ⟶ Y`
be an open immersion of `S`-schemes and `F` a sheaf of `Λ`-modules on `X`. Form the base changes
`Y' = Y ×_S S'` and `X' = X ×_Y Y'`, with the open immersion `j' : X' ⟶ Y'`. If over `S'` the
direct image `Rj'_*(F|_{X'})` is bounded constructible and its formation commutes with every base
change from a noetherian scheme, then the same holds over `S`. -/
theorem HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective
    {S S' X Y X' Y' : Scheme.{u}} (π : S' ⟶ S) [IsFinite π] [Surjective π]
    [UniversallyInjective π] (fY : Y ⟶ S) (j : X ⟶ Y) [IsOpenImmersion j] (g : Y' ⟶ Y)
    (fY' : Y' ⟶ S') (hY : IsPullback g fY' fY π) (g' : X' ⟶ X) (j' : X' ⟶ Y')
    (hX : IsPullback g' j' j g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : HasConstructibleDirectImageBaseChangeOn Λ fY' j'
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F) Set.univ) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F Set.univ :=
  .of_isFinite_of_surjective' π fY j g fY' hY g' j' hX F h

/-- Blueprint `corollary-open-direct-image-over-field--1`: Higher open direct images over a field.

Let `k` be a field, let `Λ` be a finite ring whose exponent is invertible in `k` (the blueprint
takes `Λ = 𝔽_ℓ` with `ℓ ≠ char k`), let `j : X ⟶ Y` be an open immersion of finite-type
`k`-schemes and let `F` be a constructible sheaf of `Λ`-modules on `X`. Then `Rj_* F` is
bounded constructible. This is `theorem-generic-constructibility-base-change-rj` over `S = Spec k`,
whose only nonempty open is `S` itself. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (j : X ⟶ Y)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  obtain ⟨U, ⟨s, hs⟩, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn Λ
    (𝟙 (Spec (.of k))) aY j F
  have hU : Set.range (𝟙 (Spec (.of k))) ⊆ (U : Set (Spec (.of k))) := by
    rintro x -
    rwa [Subsingleton.elim x s]
  have := (h (Spec (.of k)) (𝟙 _) hU Y X (𝟙 Y) aY (𝟙 X) j (IsPullback.id_horiz aY)
    (IsPullback.id_horiz j)).1
  exact ObjectProperty.prop_of_iso _ ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app _)) this

end Etale

end AlgebraicGeometry
