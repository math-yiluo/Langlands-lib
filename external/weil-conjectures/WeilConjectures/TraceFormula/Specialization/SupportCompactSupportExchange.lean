/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchange

/-!

# The compact-support exchange of a compactified morphism of models

Let `f : C ⟶ Y` be a morphism of `k`-schemes factored as an open immersion `h : C ⟶ C̄` followed
by a proper `p : C̄ ⟶ Y`, and similarly `f' = h' ≫ p'` over `k'`. Given models `M_C`, `M_{C̄}`,
`M_Y` and morphisms of models `φ_h : M_C ⟶ M_{C̄}` over `(h, h')` with invertible pullback
exchange `α_h` and `φ_p : M_{C̄} ⟶ M_Y` over `(p, p')` with pushforward exchange `χ_p` invertible
on bounded constructible complexes, the compact-support exchange of blueprint
`prose-E-15` (3) is
```
ν_f = χ_p⁻¹ ∘ Rp'_*(ν_h) : Rf'_! Ψ_C ⟶ Ψ_Y Rf_!
```
through `Rf_! ≅ Rp_! h_! ≅ Rp_* h_!`, with `ν_h : h'_! Ψ_C ⟶ Ψ_{C̄} h_!` the adjoint of `α_h⁻¹`
(`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).

We apply this to the support `c : C ⟶ X ⨯ X` of a correspondence contracting at `y`, `x = c₁(y)`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`): compactify
`c` as `C ⊂ C̄ ⟶ X ⨯ X` (`compactificationOverField`) and let `Z' = c̄⁻¹(x, x)`. Since the fibre
`c₁⁻¹(x)` is the point `y`, `C ∩ Z' = y` (`comap_supportClosureIdeal`), so the deformation model
of `(C, y)` is an open submodel of the one of `(C̄, Z')` and `α_h` is invertible. The legs of `c̄`
give a morphism of models to the product model `𝒳 ×_S 𝒳` of `X ⨯ X`, whose squares of special and
of geometric generic fibres are cartesian (`isPullback_deformationProdLiftSpecial`,
`isPullback_deformationProdLiftModelHom_ε`), so `χ_p` is invertible by proper base change for
nearby cycles once the morphism of total spaces is proper. That morphism is the base change of
`D_{Z'} C̄ ⟶ D_x X ×_{𝔸¹} D_x X` (`isPullback_deformationProdLiftTotal`); the properness of the
latter is taken as an instance argument.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

variable {DC DC' DP DP' : Type*} [Category DC] [Category DC'] [Category DP] [Category DP']

/-- The exchange `ν_h : Ψ_C ⋙ Dh' ⟶ Dh ⋙ Ψ_P` adjoint to the inverse of an invertible pullback
exchange `α : Ψ_P ⋙ Lh' ⟶ Lh ⋙ Ψ_C`, for adjunctions `Dh ⊣ Lh` and `Dh' ⊣ Lh'`. -/
noncomputable def lowerShriekExchangeOfInv {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Dh : DC ⥤ DP}
    {Lh : DP ⥤ DC} {Dh' : DC' ⥤ DP'} {Lh' : DP' ⥤ DC'} (adj : Dh ⊣ Lh) (adj' : Dh' ⊣ Lh')
    (α : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) [IsIso α] : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP :=
  Functor.whiskerRight ((Functor.leftUnitor ΨC).inv ≫ Functor.whiskerRight adj.unit ΨC ≫
      Functor.whiskerLeft Dh (inv α)) Dh' ≫
    Functor.whiskerLeft (Dh ⋙ ΨP) adj'.counit ≫ (Functor.rightUnitor _).hom

/-- The shape of `ν_f`: `Sp ⋙ LSf' ≅ Sp ⋙ OLS' ⋙ LStp'`, then (through the inclusions `ι`) `ν_h`
followed by `χinv` (the inverse of the proper exchange `χ_p`), then `OLS ⋙ LStp ≅ LSf`. -/
noncomputable def compactSupportExchangeAux {CC CC' CP CP' Cs Cs' Ds Ds' : Type*} [Category CC]
    [Category CC'] [Category CP] [Category CP'] [Category Cs] [Category Cs'] [Category Ds]
    [Category Ds'] {Sp : CC ⥤ CC'} {LSf' : CC' ⥤ Cs'} {LSf : CC ⥤ Cs} {Ts : Cs ⥤ Cs'}
    {OLS : CC ⥤ CP} {OLS' : CC' ⥤ CP'} {LStp : CP ⥤ Cs} {LStp' : CP' ⥤ Cs'} {ιC : CC ⥤ DC}
    {ιC' : CC' ⥤ DC'} {ιP : CP ⥤ DP} {ιP' : CP' ⥤ DP'} {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'}
    (hι : ιs'.FullyFaithful) {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Ψs : Ds ⥤ Ds'} {Dh : DC ⥤ DP}
    {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (i₁ : LSf' ≅ OLS' ⋙ LStp') (i₂ : LSf ≅ OLS ⋙ LStp)
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cO' : OLS' ⋙ ιP' ≅ ιC' ⋙ Dh') (cR' : LStp' ⋙ ιs' ≅ ιP' ⋙ Rp')
    (cO : OLS ⋙ ιP ≅ ιC ⋙ Dh) (cR : LStp ⋙ ιs ≅ ιP ⋙ Rp) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    (νh : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP) (χinv : ιP ⋙ ΨP ⋙ Rp' ⟶ ιP ⋙ Rp ⋙ Ψs) :
    Sp ⋙ LSf' ⟶ LSf ⋙ Ts :=
  Functor.whiskerLeft Sp i₁.hom ≫
    (hι.whiskeringRight CC).preimage (X := Sp ⋙ OLS' ⋙ LStp') (Y := (OLS ⋙ LStp) ⋙ Ts)
      (Functor.whiskerLeft (Sp ⋙ OLS') cR'.hom ≫
        Functor.whiskerLeft Sp (Functor.whiskerRight cO'.hom Rp') ≫
        Functor.whiskerRight cSp.hom (Dh' ⋙ Rp') ≫
        Functor.whiskerLeft ιC (Functor.whiskerRight νh Rp') ≫
        Functor.whiskerRight cO.inv (ΨP ⋙ Rp') ≫
        Functor.whiskerLeft OLS χinv ≫
        Functor.whiskerLeft OLS (Functor.whiskerRight cR.inv Ψs) ≫
        Functor.whiskerLeft (OLS ⋙ LStp) cT.inv) ≫
    Functor.whiskerRight i₂.inv Ts

end Abstract

section Compactification

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {C P Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {C' P' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom]
  [IsSeparated C'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {MC : NearbyCyclesModel C.left C'.left} {MP : NearbyCyclesModel P.left P'.left}
  {MY : NearbyCyclesModel Y.left Y'.left}
  (hMC : MC.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hMY : MY.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {f : C ⟶ Y} {h : C ⟶ P} {p : P ⟶ Y} [IsOpenImmersion h.left] [IsProper p.left]
  (w : h ≫ p = f) {f' : C' ⟶ Y'} {h' : C' ⟶ P'} {p' : P' ⟶ Y'} [IsOpenImmersion h'.left]
  [IsProper p'.left] (w' : h' ≫ p' = f')
  (φh : MC.Hom MP h.left h'.left) [IsIso (φh.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
  (φp : MP.Hom MY p.left p'.left)
  (hφp : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P.left)).ι
    (φp.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))

/-- The derived adjunction `h_! ⊣ Lh^*` along an open immersion. -/
noncomputable abbrev openImmersionAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ)
    j).ofNatIsoRight (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _ j).symm

/-- **The compact-support exchange of a compactified morphism of models** (blueprint
`prose-E-15` (3)): `ν_f = χ_p⁻¹ ∘ Rp'_*(ν_h) : Rf'_! Ψ_C ⟶ Ψ_Y Rf_!`, through
`Rf'_! ≅ Rp'_! h'_! ≅ Rp'_* h'_!` and `Rf_! ≅ Rp_* h_!`, with `ν_h` the adjoint of `α_h⁻¹`. -/
noncomputable def compactSupportExchangeOfCompactification :
    NearbyCyclesModel.boundedConstructibleNearbyCycles hMC ⋙
        boundedConstructibleLowerShriek ℓ f' ⟶
      boundedConstructibleLowerShriek ℓ f ⋙
        NearbyCyclesModel.boundedConstructibleNearbyCycles hMY :=
  compactSupportExchangeAux (ObjectProperty.fullyFaithfulι _)
    (lowerShriekCompOfEq ℓ h' p' w' ≪≫
      Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
        ℓ h') _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p'))
    (lowerShriekCompOfEq ℓ h p w ≪≫
      Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
        ℓ h) _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
    (boundedConstructibleLowerStarCompatibility ℓ _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ _)
    (boundedConstructibleLowerStarCompatibility ℓ _)
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ h.left)
      (openImmersionAdjunction ℓ h'.left) (φh.pullbackExchange _))
    (invOnSubcategory _ _ hφp)

end Compactification

section Deformation

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The special fibres of a morphism of deformation models form a cartesian square with the total
spaces. -/
lemma isPullback_deformationSpecialFibreMap {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
    {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
    (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U') :
    IsPullback (deformationSpecialToTotal X J k') (deformationSpecialFibreMap f hJ k').left
      (deformationTotalMap f hJ k') (deformationSpecialToTotal Y I k') := by
  refine IsPullback.of_bot ?_ (deformationSpecialFibreMap_toTotal f hJ k').symm
    (isPullback_deformationSpecialFibre Y I k')
  rw [Over.w, deformationTotalMap_toTrait]
  exact isPullback_deformationSpecialFibre X J k'

/-- The special fibres of the pair `(c₁, c₂) : 𝒞 ⟶ 𝒳 ×_S 𝒴` form a cartesian square with the
total spaces. -/
lemma isPullback_deformationProdLiftSpecial {X Y C : Over (Spec (.of k))}
    {I : X.left.IdealSheafData} {J : Y.left.IdealSheafData} {K : C.left.IdealSheafData}
    (c₁ : C ⟶ X)
    (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
        K.siteIdeal U')
    (c₂ : C ⟶ Y)
    (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
        K.siteIdeal U') :
    IsPullback (deformationModel C K k').i
      (prod.lift (deformationSpecialFibreMap c₁ hJ₁ k') (deformationSpecialFibreMap c₂ hJ₂ k')).left
      (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).total (deformationProdModel X I Y J k').i := by
  refine IsPullback.of_bot ?_ (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).comm_i.symm
    (isPullback_deformationProdSpecialToTotal X I Y J k')
  rw [Over.w]
  change IsPullback _ _ (deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ ≫ _) _
  rw [deformationProdLiftTotal_toTrait]
  exact isPullback_deformationSpecialFibre C K k'

/-- The morphisms of deformation spaces compose, when the first one lies over an open
immersion. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap_comp_of_isOpenImmersion
    {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) [IsOpenImmersion f] (g : X₂ ⟶ X₃)
    {I₃ : X₃.IdealSheafData} {I₂ : X₂.IdealSheafData} {I₁ : X₁.IdealSheafData}
    (hf : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₂.AffineZariskiSite⦄ (hU : U'.1 ≤ f ⁻¹ᵁ U.1),
      (I₂.siteIdeal U).map (f.appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U')
    (hg : ∀ ⦃U' : X₂.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄ (hU : U'.1 ≤ g ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map (g.appLE U.1 U'.1 hU).hom ≤ I₂.siteIdeal U')
    (hfg : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄
      (hU : U'.1 ≤ (f ≫ g) ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map ((f ≫ g).appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U') :
    IdealSheafData.deformationSpaceMap f I₂ I₁ hf ≫ IdealSheafData.deformationSpaceMap g I₃ I₂ hg =
      IdealSheafData.deformationSpaceMap (f ≫ g) I₃ I₁ hfg := by
  refine AffineZariskiSite.hom_ext_of_le_preimage (f ≫ g) I₁.coequifibered_toReesPresheaf
    fun U₁ U₃ hU ↦ ?_
  have h₁ : U₁.1 ≤ f ⁻¹ᵁ (IdealSheafData.imageSite f U₁).1 := (f.preimage_image_eq U₁.1).ge
  have h₂ : (IdealSheafData.imageSite f U₁).1 ≤ g ⁻¹ᵁ U₃.1 :=
    (f.image_mono (hU.trans (Scheme.Hom.comp_preimage f g _).le)).trans
      (f.image_preimage_le _)
  rw [IdealSheafData.deformationSpaceMap, IdealSheafData.deformationSpaceMap,
    IdealSheafData.deformationSpaceMap, AffineZariskiSite.PullbackData.ι_comparison_assoc _ _ _ h₁,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ h₂,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ hU, ← Spec.map_comp_assoc]
  congr 2
  ext : 1
  simp only [IdealSheafData.extendedReesPullbackData_map, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rw [Ideal.extendedReesAlgebraMap_comp]
  congr 1
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

variable {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) [IsOpenImmersion f.left] (g : Y ⟶ Z)
  {I₃ : Z.left.IdealSheafData} {I₂ : Y.left.IdealSheafData} {I₁ : X.left.IdealSheafData}
  (hf : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I₂.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')
  (hg : ∀ ⦃U' : Y.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (g.left.appLE U.1 U'.1 hU).hom ≤
      I₂.siteIdeal U')
  (hfg : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ (f ≫ g).left ⁻¹ᵁ U.1),
    (I₃.siteIdeal U).map ((f ≫ g).left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')

lemma deformationTotalMap_comp_of_isOpenImmersion :
    deformationTotalMap f hf k' ≫ deformationTotalMap g hg k' =
      deformationTotalMap (f ≫ g) hfg k' := by
  apply pullback.hom_ext
  · change _ ≫ deformationTotalToSpace _ _ k' = _ ≫ deformationTotalToSpace _ _ k'
    rw [Category.assoc, deformationTotalMap_toSpace, deformationTotalMap_toSpace_assoc,
      deformationTotalMap_toSpace]
    exact congrArg (deformationTotalToSpace X I₁ k' ≫ ·)
      (IdealSheafData.deformationSpaceMap_comp_of_isOpenImmersion f.left g.left hf hg hfg)
  · change _ ≫ deformationTotalToTrait _ _ k' = _ ≫ deformationTotalToTrait _ _ k'
    rw [Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait,
      deformationTotalMap_toTrait]

lemma deformationSpecialFibreMap_comp_of_isOpenImmersion :
    deformationSpecialFibreMap f hf k' ≫ deformationSpecialFibreMap g hg k' =
      deformationSpecialFibreMap (f ≫ g) hfg k' := by
  ext1
  apply pullback.hom_ext
  · change _ ≫ deformationSpecialToTotal _ _ k' = _ ≫ deformationSpecialToTotal _ _ k'
    rw [Over.comp_left, Category.assoc, deformationSpecialFibreMap_toTotal,
      deformationSpecialFibreMap_toTotal_assoc, deformationTotalMap_comp_of_isOpenImmersion,
      deformationSpecialFibreMap_toTotal]
  · change _ ≫ (deformationSpecialFibre Z I₃ k').hom = _ ≫ (deformationSpecialFibre Z I₃ k').hom
    simp only [Over.w]

omit [IsOpenImmersion f.left] in
lemma deformationSpecialFibreMap_congr {f' : X ⟶ Z} (e : f' = f ≫ g)
    (hf' : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f'.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (f'.left.appLE U.1 U'.1 hU).hom ≤
        I₁.siteIdeal U') :
    deformationSpecialFibreMap f' hf' k' = deformationSpecialFibreMap (f ≫ g) hfg k' := by
  subst e
  rfl

omit [IsOpenImmersion f.left] in
/-- The geometric generic fibre of the deformation model is `X ×_k Spec Ω`, with the bottom map the
identification `ε` of the trait model (`isPullback_deformationModel_ε`). -/
lemma isPullback_deformationModel_ε_traitModel (I : X.left.IdealSheafData) :
    IsPullback (deformationModel X I k').ε
      (pullback.snd (deformationTotalToTrait X I k') (traitGenericPoint k')) X.hom
      (traitModel k k').ε := by
  rw [← traitModel_j_traitToBase]
  exact isPullback_deformationModel_ε k' I

section Product

variable (X Y : Over (Spec (.of k))) (I : X.left.IdealSheafData) (J : Y.left.IdealSheafData)

/-- The geometric generic fibre of the product model is the fibre product over `Spec Ω` of those
of the factors. -/
lemma isPullback_deformationProdGeneric :
    IsPullback (deformationProdFstGeneric X I Y J k') (deformationProdSndGeneric X I Y J k')
      (pullback.snd (deformationTotalToTrait X I k') (traitGenericPoint k'))
      (pullback.snd (deformationTotalToTrait Y J k') (traitGenericPoint k')) := by
  have hFs : deformationProdFstGeneric X I Y J k' ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hSs : deformationProdSndGeneric X I Y J k' ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hQ₁ : IsPullback (deformationProdFstGeneric X I Y J k')
      (deformationProdGenericToTotal X I Y J k') (deformationGenericToTotal X I k')
      (pullback.fst _ _) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (deformationTotalToTrait X I k') (traitGenericPoint k')).flip
    rw [hFs]
    exact (IsPullback.of_hasPullback (deformationProdTotalToTrait X I Y J k')
      (traitGenericPoint k')).flip
  have hQ := hQ₁.paste_vert (IsPullback.of_hasPullback (deformationTotalToTrait X I k')
    (deformationTotalToTrait Y J k'))
  refine IsPullback.of_bot ?_ (hFs.trans hSs.symm)
    (IsPullback.of_hasPullback (deformationTotalToTrait Y J k') (traitGenericPoint k')).flip
  rw [show deformationProdSndGeneric X I Y J k' ≫
      pullback.fst (deformationTotalToTrait Y J k') (traitGenericPoint k') =
      deformationProdGenericToTotal X I Y J k' ≫ pullback.snd _ _ from pullback.lift_fst _ _ _,
    ← pullback.condition]
  exact hQ

/-- The geometric generic fibre of the product model is `(X ⨯ Y) ×_k Spec Ω`, the identification
`ε` being the first projection. -/
lemma isPullback_deformationProdModel_ε :
    IsPullback (deformationProdModel X I Y J k').ε
      (pullback.snd (deformationProdTotalToTrait X I Y J k') (traitGenericPoint k')) (X ⨯ Y).hom
      (traitModel k k').ε := by
  have h := IsPullback.of_isPullback_of_baseChange (z := (deformationProdModel X I Y J k').ε)
    (isPullback_deformationModel_ε_traitModel k' (X := X) I)
    (isPullback_deformationModel_ε_traitModel k' (X := Y) J)
    (IsPullback.id_vert (traitModel k k').ε) (Category.comp_id _) (Category.comp_id _)
    (isPullback_deformationModel_ε_traitModel k' (X := X) I).w.symm
    (isPullback_deformationModel_ε_traitModel k' (X := Y) J).w.symm
    (isPullback_prod_left X Y) (isPullback_deformationProdGeneric k' X Y I J)
    (deformationProdFstModelHom X I Y J k').comm_ε.symm
    (deformationProdSndModelHom X I Y J k').comm_ε.symm
  rwa [Over.w, show deformationProdFstGeneric X I Y J k' ≫ pullback.snd _ _ = pullback.snd _ _ from
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)] at h

/-- The projection `𝒳 ×_S 𝒴 ⟶ D_I X ×_{𝔸¹} D_J Y`. -/
noncomputable def deformationProdTotalToSpaces :
    deformationProdTotal X I Y J k' ⟶
      pullback (deformationSpaceToAffineLine X I) (deformationSpaceToAffineLine Y J) :=
  pullback.map _ _ _ _ (deformationTotalToSpace X I k') (deformationTotalToSpace Y J k')
    (traitToAffineLine k k') (isPullback_deformationTotal X I k').w.symm
    (isPullback_deformationTotal Y J k').w.symm

/-- `𝒳 ×_S 𝒴 = (D_I X ×_{𝔸¹} D_J Y) ×_{𝔸¹} S`. -/
lemma isPullback_deformationProdTotalToSpaces :
    IsPullback (deformationProdTotalToSpaces k' X Y I J) (deformationProdTotalToTrait X I Y J k')
      (pullback.fst _ _ ≫ deformationSpaceToAffineLine X I) (traitToAffineLine k k') :=
  IsPullback.of_isPullback_of_baseChange (isPullback_deformationTotal X I k')
    (isPullback_deformationTotal Y J k') (IsPullback.id_vert (traitToAffineLine k k'))
    (Category.comp_id _) (Category.comp_id _) (isPullback_deformationTotal X I k').w.symm
    (isPullback_deformationTotal Y J k').w.symm (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

variable {X Y} {C : Over (Spec (.of k))} {K : C.left.IdealSheafData} {I J} (c₁ : C ⟶ X)
  (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  (c₂ : C ⟶ Y)
  (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')

/-- The square of geometric generic fibres of `(c₁, c₂) : 𝒞 ⟶ 𝒳 ×_S 𝒴` over `(c₁, c₂)` is
cartesian: both are base changes to `Spec Ω`. -/
lemma isPullback_deformationProdLiftModelHom_ε :
    IsPullback (deformationModel C K k').ε (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).generic
      (prod.lift c₁ c₂).left (deformationProdModel X I Y J k').ε := by
  refine IsPullback.of_bot ?_ (deformationProdLiftModelHom k' c₁ hJ₁ c₂ hJ₂).comm_ε.symm
    (isPullback_deformationProdModel_ε k' X Y I J)
  rw [Over.w]
  change IsPullback _ (deformationProdLiftGeneric k' c₁ hJ₁ c₂ hJ₂ ≫ pullback.snd _ _) _ _
  rw [show deformationProdLiftGeneric k' c₁ hJ₁ c₂ hJ₂ ≫ pullback.snd _ _ = pullback.snd _ _ from
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)]
  exact isPullback_deformationModel_ε_traitModel k' (X := C) K


/-- The morphism `(c₁, c₂) : D_K C ⟶ D_I X ×_{𝔸¹} D_J Y` of deformation spaces. -/
noncomputable def deformationSpaceProdLift :
    K.deformationSpace ⟶
      pullback (deformationSpaceToAffineLine X I) (deformationSpaceToAffineLine Y J) :=
  pullback.lift (IdealSheafData.deformationSpaceMap c₁.left I K hJ₁)
    (IdealSheafData.deformationSpaceMap c₂.left J K hJ₂) (by
      rw [deformationSpaceMap_deformationSpaceToAffineLine,
        deformationSpaceMap_deformationSpaceToAffineLine])

/-- The morphism of total spaces `𝒞 ⟶ 𝒳 ×_S 𝒴` is the base change along `S ⟶ 𝔸¹` of
`D_K C ⟶ D_I X ×_{𝔸¹} D_J Y`. -/
lemma isPullback_deformationProdLiftTotal :
    IsPullback (deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂) (deformationTotalToSpace C K k')
      (deformationProdTotalToSpaces k' X Y I J) (deformationSpaceProdLift c₁ hJ₁ c₂ hJ₂) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_deformationProdTotalToSpaces k' X Y I J).flip
  · rw [deformationProdLiftTotal_toTrait, deformationSpaceProdLift, pullback.lift_fst_assoc,
      deformationSpaceMap_deformationSpaceToAffineLine]
    exact (isPullback_deformationTotal C K k').flip
  · apply pullback.hom_ext
    · rw [Category.assoc, deformationProdTotalToSpaces, pullback.lift_fst, deformationProdLiftTotal,
        pullback.lift_fst_assoc, deformationTotalMap_toSpace, Category.assoc,
        deformationSpaceProdLift, pullback.lift_fst]
    · rw [Category.assoc, deformationProdTotalToSpaces, pullback.lift_snd, deformationProdLiftTotal,
        pullback.lift_snd_assoc, deformationTotalMap_toSpace, Category.assoc,
        deformationSpaceProdLift, pullback.lift_snd]

/-- If `D_K C ⟶ D_I X ×_{𝔸¹} D_J Y` is proper, so is the morphism of total spaces. -/
lemma isProper_deformationProdLiftTotal
    [IsProper (deformationSpaceProdLift c₁ hJ₁ c₂ hJ₂)] :
    IsProper (deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂) :=
  MorphismProperty.of_isPullback (isPullback_deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂).flip
    inferInstance
end Product

end Deformation

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']

variable (c) in
/-- The compactification `C ⊂ C̄ ⟶ X ⨯ X` of the support map of `c`. -/
noncomputable abbrev supportCompactification : Compactification c.support.left :=
  compactificationOverField c.support

variable (c) in
/-- The compactification `C̄` of the support of `c`, as a `k`-scheme. -/
noncomputable def supportClosure : Over (Spec (.of k)) :=
  Over.mk ((supportCompactification c).g ≫ (X ⨯ X).hom)

instance : LocallyOfFiniteType (supportClosure c).hom :=
  inferInstanceAs (LocallyOfFiniteType (_ ≫ _))

instance : QuasiCompact (supportClosure c).hom :=
  inferInstanceAs (QuasiCompact (_ ≫ _))

instance : IsSeparated (supportClosure c).hom :=
  inferInstanceAs (IsSeparated (_ ≫ _))

variable (c) in
/-- The open immersion `h : C ⟶ C̄`. -/
noncomputable def supportClosureι : c.C ⟶ supportClosure c :=
  Over.homMk (supportCompactification c).i (by
    change _ ≫ _ ≫ _ = _
    rw [← Category.assoc, ← (supportCompactification c).comm, Over.w])

instance : IsOpenImmersion (supportClosureι c).left :=
  inferInstanceAs (IsOpenImmersion (supportCompactification c).i)

variable (c) in
/-- The proper map `p : C̄ ⟶ X ⨯ X` extending the support map. -/
noncomputable def supportClosureMap : supportClosure c ⟶ X ⨯ X :=
  Over.homMk (supportCompactification c).g rfl

instance : IsProper (supportClosureMap c).left :=
  inferInstanceAs (IsProper (supportCompactification c).g)

variable (c) in
@[reassoc (attr := simp)]
lemma supportClosureι_map : supportClosureι c ≫ supportClosureMap c = c.support :=
  Over.OverMorphism.ext (supportCompactification c).comm.symm

variable (c y) in
/-- The ideal of `Z' = c̄⁻¹(x, x) ⊆ C̄`, the preimage of the rational point `(x, x)` of `X ⨯ X`,
`x = c₁(y)`. -/
noncomputable def supportClosureIdeal : (supportClosure c).left.IdealSheafData :=
  ((y ≫ c.c₁) ≫ diag X).left.ker.comap (supportClosureMap c).left

/-- Sitewise inclusions of ideals from an inclusion `g⁻¹ I ⊆ J`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_siteIdeal_le_of_comap_le
    {X' Y' : Scheme.{u}} (g : X' ⟶ Y') {I : Y'.IdealSheafData} {J : X'.IdealSheafData}
    (hle : I.comap g ≤ J) ⦃U' : X'.AffineZariskiSite⦄ ⦃U : Y'.AffineZariskiSite⦄
    (hU : U'.1 ≤ g ⁻¹ᵁ U.1) : (I.siteIdeal U).map (g.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U' :=
  (IdealSheafData.map_siteIdeal_le_comap g I hU).trans (hle ⟨U'.1, U'.2⟩)

include hc in
/-- The contracting hypothesis: the fibre `c₁⁻¹(x)` is the reduced point `y`, so
`ker y = c₁⁻¹ (ker x)`. -/
lemma ker_eq_comap_c₁ : y.left.ker = (y ≫ c.c₁).left.ker.comap c.c₁.left := by
  have hP := hc.isPullback.map (Over.forget _)
  simp only [Over.forget_map] at hP
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion, ← hP.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

include hc in
lemma comp_support_eq : y ≫ c.support = (y ≫ c.c₁) ≫ diag X := by
  apply prod.hom_ext <;> simp [hc.comp_c₁_eq_comp_c₂]

include hc in
/-- The preimage of `Z'` in `C` is the point `y`: `C ∩ c̄⁻¹(x, x) = c⁻¹(x, x) = y`. -/
lemma comap_supportClosureIdeal :
    y.left.ker = (supportClosureIdeal c y).comap (supportClosureι c).left := by
  rw [supportClosureIdeal, ← IdealSheafData.comap_comp, ← Over.comp_left, supportClosureι_map]
  refine le_antisymm ?_ ?_
  · have e : c.c₁.left = c.support.left ≫ (prod.fst : X ⨯ X ⟶ X).left := by
      rw [← Over.comp_left, c.support_fst]
    rw [hc.ker_eq_comap_c₁, e, IdealSheafData.comap_comp]
    refine IdealSheafData.comap_mono (f := _) ?_
    rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, Category.assoc, diag, prod.lift_fst,
      Category.comp_id]
  · rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, hc.comp_support_eq]

variable (c y) in
/-- The ideal of `x` pulls back along `c̄ ≫ q` into `Z'`, for a retraction `q` of the diagonal. -/
lemma map_siteIdeal_le_supportClosureIdeal (q : X ⨯ X ⟶ X) (hq : diag X ≫ q = 𝟙 X) :
    ∀ ⦃U' : (supportClosure c).left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (supportClosureMap c ≫ q).left ⁻¹ᵁ U.1),
      ((y ≫ c.c₁).left.ker.siteIdeal U).map ((supportClosureMap c ≫ q).left.appLE U.1 U'.1
        hU).hom ≤ (supportClosureIdeal c y).siteIdeal U' := by
  refine IdealSheafData.map_siteIdeal_le_of_comap_le _ ?_
  rw [show (supportClosureMap c ≫ q).left = (supportClosureMap c).left ≫ q.left from rfl,
    IdealSheafData.comap_comp, supportClosureIdeal]
  refine IdealSheafData.comap_mono (f := _) ?_
  rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, Category.assoc, hq, Category.comp_id]

include hc in
/-- The ideal `Z'` pulls back along `h : C ⟶ C̄` into the ideal of `y`. -/
lemma map_siteIdeal_le_ker :
    ∀ ⦃U' : c.C.left.AffineZariskiSite⦄ ⦃U : (supportClosure c).left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (supportClosureι c).left ⁻¹ᵁ U.1),
      ((supportClosureIdeal c y).siteIdeal U).map ((supportClosureι c).left.appLE U.1 U'.1
        hU).hom ≤ y.left.ker.siteIdeal U' :=
  IdealSheafData.map_siteIdeal_le_of_comap_le _ hc.comap_supportClosureIdeal.ge

variable (c) in
lemma prodLift_supportClosureMap :
    prod.lift (supportClosureMap c ≫ prod.fst) (supportClosureMap c ≫ prod.snd) =
      supportClosureMap c :=
  prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)

variable (c y) in
lemma map_siteIdeal_le_closureLeg₁ :
    ∀ ⦃U' : (supportClosure c).left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (supportClosureMap c ≫ prod.fst).left ⁻¹ᵁ U.1),
      ((y ≫ c.c₁).left.ker.siteIdeal U).map ((supportClosureMap c ≫ prod.fst).left.appLE U.1 U'.1
        hU).hom ≤ (supportClosureIdeal c y).siteIdeal U' :=
  map_siteIdeal_le_supportClosureIdeal c y prod.fst (by rw [diag, prod.lift_fst])

variable (c y) in
lemma map_siteIdeal_le_closureLeg₂ :
    ∀ ⦃U' : (supportClosure c).left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (supportClosureMap c ≫ prod.snd).left ⁻¹ᵁ U.1),
      ((y ≫ c.c₁).left.ker.siteIdeal U).map ((supportClosureMap c ≫ prod.snd).left.appLE U.1 U'.1
        hU).hom ≤ (supportClosureIdeal c y).siteIdeal U' :=
  map_siteIdeal_le_supportClosureIdeal c y prod.snd (by rw [diag, prod.lift_snd])

variable (c y) in
/-- The open immersion of deformation models `𝒞 ⟶ 𝒞̄ = D_{Z'} C̄ ×_{𝔸¹} S` over `h : C ⟶ C̄`. -/
noncomputable def supportClosureOpenModelHom :=
  deformationModelHom (supportClosureι c) hc.map_siteIdeal_le_ker k'

variable (c y) in
/-- The morphism of deformation models `𝒞̄ ⟶ 𝒳 ×_S 𝒳` over `c̄ : C̄ ⟶ X ⨯ X`, built from the two
legs `c̄₁, c̄₂` of `c̄`. -/
noncomputable def supportClosureProperModelHom :=
  deformationProdLiftModelHom k' (supportClosureMap c ≫ prod.fst)
    (map_siteIdeal_le_closureLeg₁ c y) (supportClosureMap c ≫ prod.snd)
    (map_siteIdeal_le_closureLeg₂ c y)

variable (c y) in
/-- The morphism `D_{Z'} C̄ ⟶ D_x X ×_{𝔸¹} D_x X` of deformation spaces given by the legs of
`c̄`. It is proper if `D_{Z'} C̄ ⟶ C̄ ×_{X ⨯ X} (D_x X ×_{𝔸¹} D_x X)` is a closed immersion (the
extended Rees algebra of a sum of ideals is generated by those of the summands). -/
noncomputable abbrev supportClosureSpaceMap :=
  deformationSpaceProdLift (supportClosureMap c ≫ prod.fst) (map_siteIdeal_le_closureLeg₁ c y)
    (supportClosureMap c ≫ prod.snd) (map_siteIdeal_le_closureLeg₂ c y)

variable (c y) in
/-- The special fibre `p' : C̄' ⟶ X' ⨯ X'` of `c̄`. -/
noncomputable abbrev supportClosureSpecialMap :=
  prod.lift (deformationSpecialFibreMap (supportClosureMap c ≫ prod.fst)
    (map_siteIdeal_le_closureLeg₁ c y) k')
    (deformationSpecialFibreMap (supportClosureMap c ≫ prod.snd)
      (map_siteIdeal_le_closureLeg₂ c y) k')

/-- The special fibre `h' : C' ⟶ C̄'` of `h`. -/
noncomputable abbrev supportClosureSpecialι :=
  deformationSpecialFibreMap (supportClosureι c) hc.map_siteIdeal_le_ker k'

instance : IsProper (prod.lift (supportClosureMap c ≫ prod.fst)
    (supportClosureMap c ≫ prod.snd)).left := by
  rw [prodLift_supportClosureMap]
  infer_instance

instance : IsOpenImmersion (hc.supportClosureSpecialι k').left :=
  have : IsOpenImmersion (deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k') :=
    isOpenImmersion_deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k'
      hc.comap_supportClosureIdeal
  MorphismProperty.of_isPullback
    (isPullback_deformationSpecialFibreMap k' (supportClosureι c) hc.map_siteIdeal_le_ker) this

lemma isPullback_supportClosureSpecialMap :
    IsPullback (deformationModel (supportClosure c) (supportClosureIdeal c y) k').i
      (supportClosureSpecialMap c y k').left (supportClosureProperModelHom c y k').total
      (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k').i :=
  isPullback_deformationProdLiftSpecial k' _ _ _ _

lemma isProper_supportClosureSpecialMap
    (hP : IsProper (supportClosureProperModelHom c y k').total) :
    IsProper (supportClosureSpecialMap c y k').left :=
  MorphismProperty.of_isPullback (isPullback_supportClosureSpecialMap k') hP

instance isIso_supportClosureOpenModelHom_pullbackExchange :
    IsIso ((supportClosureOpenModelHom c y hc k').pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)) :=
  isIso_deformationModelHom_pullbackExchange (supportClosureι c) hc.map_siteIdeal_le_ker k' _
    hc.comap_supportClosureIdeal

variable [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']

/-- The special fibre of `h' ≫ p'` is the support of the specialized correspondence. -/
lemma supportClosureSpecialι_comp :
    hc.supportClosureSpecialι k' ≫ supportClosureSpecialMap c y k' =
      (hc.specialCorrespondence k').support := by
  have h₁ := Correspondence.ker_map_le_of_comp_eq (y := y)
    (supportClosureι c ≫ supportClosureMap c ≫ prod.fst) (y ≫ c.c₁) (by simp)
  have h₂ := Correspondence.ker_map_le_of_comp_eq (y := y)
    (supportClosureι c ≫ supportClosureMap c ≫ prod.snd) (y ≫ c.c₁)
    (by simp [hc.comp_c₁_eq_comp_c₂])
  apply prod.hom_ext
  · rw [Category.assoc, prod.lift_fst, Correspondence.support_fst,
      deformationSpecialFibreMap_comp_of_isOpenImmersion k' (hfg := h₁)]
    exact (deformationSpecialFibreMap_congr k' (supportClosureι c)
      (supportClosureMap c ≫ prod.fst) h₁ (f' := c.c₁) (by simp) hc.ker_map_le_c₁).symm
  · rw [Category.assoc, prod.lift_snd, Correspondence.support_snd,
      deformationSpecialFibreMap_comp_of_isOpenImmersion k' (hfg := h₂)]
    exact (deformationSpecialFibreMap_congr k' (supportClosureι c)
      (supportClosureMap c ≫ prod.snd) h₂ (f' := c.c₂) (by simp) hc.ker_map_le_c₂).symm

omit [Fact (ringChar k').Prime] [IsSepClosed k'] in
/-- The proper exchange `χ_p` of `𝒞̄ ⟶ 𝒳 ×_S 𝒳` is invertible on bounded constructible
complexes, if the morphism of total spaces is proper. -/
lemma isIsoOn_supportClosureProperModelHom_pushforwardExchange
    (hP : IsProper (supportClosureProperModelHom c y k').total) :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (supportClosure c).left)).ι
      ((supportClosureProperModelHom c y k').pushforwardExchange
        (Profinite.padicAlgClRingObj ℓ)) :=
  have := isNoetherian_of_locallyOfFiniteType (X ⨯ X).hom
  fun K ↦ (supportClosureProperModelHom c y k').isIso_pushforwardExchange_app_of_isProper
    (X ⨯ X).hom (isTraitModel_deformationModel _ _ k').exists_over
    (isTraitModel_deformationProdModel _ _ _ _ k').exists_over
    (isPullback_supportClosureSpecialMap k')
    (isPullback_deformationProdLiftModelHom_ε k' _ _ _ _) K.property

/-- **The compact-support exchange `ν_c` of the support** (blueprint `prose-E-15`
(3)), for the compactification `C ⊂ C̄ ⟶ X ⨯ X` of the support and `Z' = c̄⁻¹(x, x)`:
`ν_c = χ_p⁻¹ ∘ Rp'_*(ν_h)` (`compactSupportExchangeOfCompactification`), with `α_h` invertible
since `C ∩ Z' = y` (`comap_supportClosureIdeal`) and `χ_p` invertible by proper base change for
nearby cycles. It assumes that the morphism `D_{Z'} C̄ ⟶ D_x X ×_{𝔸¹} D_x X` of deformation
spaces (`supportClosureSpaceMap`) is proper. -/
noncomputable def supportCompactSupportExchange [IsProper (supportClosureSpaceMap c y)] :
    hc.SupportCompactSupportExchange (ℓ := ℓ) k' :=
  have hP : IsProper (supportClosureProperModelHom c y k').total :=
    isProper_deformationProdLiftTotal k' _ _ _ _
  have := isProper_supportClosureSpecialMap k' hP
  compactSupportExchangeOfCompactification ℓ
    (MC := deformationModel c.C y.left.ker k')
    (MY := deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
    ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel c.C y.left.ker k')
      (deformationModel_exists_comp_ε c.C y.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k'))
    (f := c.support) (h := supportClosureι c)
    (by rw [prodLift_supportClosureMap, supportClosureι_map])
    (f' := (hc.specialCorrespondence k').support) (h' := hc.supportClosureSpecialι k')
    (hc.supportClosureSpecialι_comp k') (supportClosureOpenModelHom c y hc k')
    (supportClosureProperModelHom c y k')
    (isIsoOn_supportClosureProperModelHom_pushforwardExchange k' hP)

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
