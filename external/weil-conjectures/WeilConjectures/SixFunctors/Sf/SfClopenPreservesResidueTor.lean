/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.Algebra.Homology.Ringed.RingedEquivalenceDerivedTensorComparison
import WeilConjectures.SixFunctors.Sf.SfClopenScalarQuotientComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Objectwise residue Tor bounds under clopen restriction

Source: Stacks Project, Tags 08FZ, 06YY and 00Y0.
(blueprint: lem-sf-clopen-preserves-residue-tor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- These functors are used only through their named comparison isomorphism.
attribute [local irreducible] scalarReductionDerivedExtension sfClopenDerivedRestriction

universe c h c' h' r w w'

private theorem torAmplitude_iso
    {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    {X Y : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))}
    (e : X ≅ Y) (a b : ℤ) (hX : HasRingedSiteTorAmplitudeOfUniverses R X a b) :
    HasRingedSiteTorAmplitudeOfUniverses R Y a b := by
  refine ⟨hX.1, ?_⟩
  intro L q hq
  exact (hX.2 L q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).mapIso
      (Iso.prod e.symm (Iso.refl _))))

private theorem torAmplitude_equivalence
    {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
    {D : Type c'} [Category.{h'} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w'} (ringedSiteModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (F : ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      ringedSiteModules.{r}
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [F.Additive] [F.IsEquivalence]
    (τ : ∀ X N, Nonempty (F.mapDerivedCategory.obj
      ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).obj
        (X, (DerivedCategory.singleFunctor _ 0).obj N)) ≅
      (SheafOfModules.siteDerivedTensorIndependentCoefficients K S).obj
        (F.mapDerivedCategory.obj X, (DerivedCategory.singleFunctor _ 0).obj (F.obj N))))
    (X : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (a b : ℤ) (hX : HasRingedSiteTorAmplitudeOfUniverses R X a b) :
    HasRingedSiteTorAmplitudeOfUniverses S (F.mapDerivedCategory.obj X) a b := by
  refine ⟨hX.1, ?_⟩
  intro L q hq
  let N := F.objPreimage L
  let i := F.objObjPreimageIso L
  let e₀ := (DerivedCategory.singleFunctor _ 0).mapIso i
  obtain ⟨t⟩ := τ X N
  let e₁ := (SheafOfModules.siteDerivedTensorIndependentCoefficients K S).mapIso
    (Iso.prod (Iso.refl (F.mapDerivedCategory.obj X)) e₀.symm) ≪≫ t.symm
  let e₂ := (DerivedCategory.homologyFunctor _ q).mapIso e₁ ≪≫
    ((F.mapDerivedCategoryHomologyFunctorIso q).app
      ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).obj
        (X, (DerivedCategory.singleFunctor _ 0).obj N))).symm
  exact (F.map_isZero (hX.2 N q hq)).of_iso e₂

private theorem torAmplitude_cocontinuousEquivalence
    {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
    {D : Type c'} [Category.{h'} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w'} (ringedSiteModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (f : D ⥤ C) [f.IsContinuous K J] [f.IsCocontinuous K J]
    (c₀ : (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S ≅
      (f.sheafPushforwardContinuous RingCat.{r} K J).obj
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    [hAdd : (SheafOfModules.pushforward.{r} c₀.hom).Additive]
    [hEquiv : (SheafOfModules.pushforward.{r} c₀.hom).IsEquivalence]
    (X : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (a b : ℤ) (hX : HasRingedSiteTorAmplitudeOfUniverses R X a b) :
    HasRingedSiteTorAmplitudeOfUniverses S
      ((SheafOfModules.pushforward.{r} c₀.hom).mapDerivedCategory.obj X) a b := by
  let F := SheafOfModules.pushforward.{r} c₀.hom
  obtain ⟨m⟩ := SheafOfModules.ringed_cocontinuous_monoidal f S R c₀
  let : F.Monoidal := m
  exact torAmplitude_equivalence R S F
    (SheafOfModules.ringedEquivalence_derivedTensorComparison R S F
      (Functor.Monoidal.μNatIso F).symm) X a b hX

private theorem slicePost_isEquivalence {T : Scheme.{t}} (U : T.Opens)
    (V : U.toScheme.ProEt) :
    (Over.post (X := V) (sfClopenSiteInclusion U)).IsEquivalence := by
  let W := (sfClopenSiteInclusion U).obj V
  let f := Over.post (X := V) (sfClopenSiteInclusion U)
  let g := (Scheme.ProEt.sliceEquiv T W).functor
  let : g.IsEquivalence := (Scheme.ProEt.sliceEquiv T W).isEquivalence_functor
  let i : f ⋙ g ≅ (Scheme.ProEt.sliceEquiv U.toScheme V).functor := Iso.refl _
  let : (f ⋙ g).IsEquivalence :=
    ((Scheme.ProEt.sliceEquiv U.toScheme V).changeFunctor i.symm).isEquivalence_functor
  exact Functor.isEquivalence_of_comp_right f g

private theorem sliceModuleTransport
    {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [hInv : e.inverse.IsContinuous K J] [hFor : e.functor.IsContinuous J K]
    (R : Sheaf J RingCat.{max u (t + 1)}) (S : Sheaf K RingCat.{max u (t + 1)})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).obj R) :
    (SheafOfModules.pushforward.{max u (t + 1)}
      (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    erw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    erw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    erw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      erw [← Functor.map_comp, ← op_comp]
      simp
    erw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  let : e.symm.functor.IsContinuous K J := hInv
  let : e.symm.inverse.IsContinuous J K := hFor
  let q := SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂
  exact q.isEquivalence_functor

private def moduleRestrictionSliceIso
    {C : Type c} [Category.{h} C] {D : Type c'} [Category.{h'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (j : C ⥤ D) [j.IsContinuous J K] (V : C)
    [(Over.post (X := V) j).IsContinuous (J.over V) (K.over (j.obj V))]
    (R : Sheaf K RingCat.{r}) (S : Sheaf J RingCat.{r})
    (c₀ : S ≅ (j.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    SheafOfModules.overFunctor.{r} R (j.obj V) ⋙
        SheafOfModules.pushforward.{r} (F := Over.post (X := V) j)
          ((J.overPullback RingCat.{r} V).mapIso c₀).hom ≅
      (SheafOfModules.pushforward.{r} (F := j) (𝟙 _) ⋙
        SheafOfModules.restrictScalars c₀.hom) ⋙
          SheafOfModules.overFunctor.{r} S V :=
  Iso.refl _

private theorem clopenFinite_preservesTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (d : SfClopenCoefficientRestriction l E T U)
    (X : DerivedCategory (scalarReductionTarget l E T 0)) (a b : ℤ)
    (hX : SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) T X a b) :
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) U.toScheme
      ((sfClopenFiniteDerivedRestriction d 0).obj X) a b := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  intro V
  let J := Scheme.ProEt.topology U.toScheme
  let K := Scheme.ProEt.topology T
  let W := (sfClopenSiteInclusion U).obj V
  let f := Over.post (X := V) (sfClopenSiteInclusion U)
  let : f.IsEquivalence := slicePost_isEquivalence U V
  let : (sfClopenSiteInclusion U).IsCocontinuous J K :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale U.ι)
  let : f.IsCocontinuous (J.over V) (K.over W) := inferInstance
  let : f.IsContinuous (J.over V) (K.over W) :=
    (Functor.isContinuous_iff_coverPreserving).2
      ((Scheme.ProEt.coverPreserving_overMap
        (inferInstance : WeaklyEtale U.ι)).overPost V)
  let e := f.asEquivalence
  let : e.functor.IsCocontinuous (J.over V) (K.over W) :=
    inferInstanceAs (f.IsCocontinuous (J.over V) (K.over W))
  let : e.functor.IsContinuous (J.over V) (K.over W) :=
    inferInstanceAs (f.IsContinuous (J.over V) (K.over W))
  let : e.inverse.IsContinuous (K.over W) (J.over V) :=
    e.toAdjunction.isContinuous_of_isCocontinuous _ _
  let : e.symm.functor.IsContinuous (K.over W) (J.over V) :=
    inferInstanceAs (e.inverse.IsContinuous (K.over W) (J.over V))
  let : e.symm.inverse.IsContinuous (J.over V) (K.over W) :=
    inferInstanceAs (e.functor.IsContinuous (J.over V) (K.over W))
  let R := integralCoefficientCommRingSheaf l E T 0
  let S := integralCoefficientCommRingSheaf l E U.toScheme 0
  let c : (integralCoefficientSheaf l E U.toScheme 0).over V ≅
      (f.sheafPushforwardContinuous RingCat.{max u (t + 1)} _ _).obj
        ((integralCoefficientSheaf l E T 0).over W) :=
    (J.overPullback RingCat.{max u (t + 1)} V).mapIso (d.finite 0)
  let F := SheafOfModules.pushforward.{max u (t + 1)} (F := f) c.hom
  let : F.IsEquivalence := sliceModuleTransport (K.over W) (J.over V) e.symm
    ((integralCoefficientSheaf l E T 0).over W)
    ((integralCoefficientSheaf l E U.toScheme 0).over V) c
  let : F.Additive := by
    constructor
    intro A B x y
    ext Z z
    rfl
  let : HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((integralCoefficientSheaf l E T 0).over W)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((integralCoefficientSheaf l E U.toScheme 0).over V)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (K.over W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (R.over W))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (J.over V)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (S.over V))) :=
    HasDerivedCategory.standard _
  let G := SheafOfModules.overFunctor.{max u (t + 1)}
    (integralCoefficientSheaf l E T 0) W
  let H := SheafOfModules.overFunctor.{max u (t + 1)}
    (integralCoefficientSheaf l E U.toScheme 0) V
  let B := sfClopenModuleRestriction U _ _ (d.finite 0)
  let : B.Additive := d.finite_additive 0
  let : PreservesFiniteLimits B := d.finite_limits 0
  let : PreservesFiniteColimits B := d.finite_colimits 0
  have eG := ringedOverFunctor_exactGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
    (integralCoefficientSheaf l E T 0) W
  have eH := ringedOverFunctor_exactGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
    (integralCoefficientSheaf l E U.toScheme 0) V
  let : G.Additive := eG.1
  let : PreservesFiniteLimits G := eG.2.1
  let : PreservesFiniteColimits G := eG.2.2
  let : H.Additive := eH.1
  let : PreservesFiniteLimits H := eH.2.1
  let : PreservesFiniteColimits H := eH.2.2
  let n : G ⋙ F ≅ B ⋙ H := moduleRestrictionSliceIso J K
    (sfClopenSiteInclusion U) V (integralCoefficientSheaf l E T 0)
      (integralCoefficientSheaf l E U.toScheme 0) (d.finite 0)
  let nD : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      B.mapDerivedCategory ⋙ H.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso G F ≪≫
    Functor.mapDerivedCategoryNatIso n ≪≫ (Functor.mapDerivedCategoryCompIso B H).symm
  have ht := torAmplitude_cocontinuousEquivalence (R.over W) (S.over V) f c
    (hAdd := inferInstanceAs (F.Additive)) (hEquiv := inferInstanceAs (F.IsEquivalence))
    (G.mapDerivedCategory.obj X)
    a b (hX W)
  have ht' := torAmplitude_iso (S.over V)
    (nD.app X) a b ht
  exact ht'

/-- Objectwise residue Tor bounds under clopen restriction.

Source: Stacks Project, Tags 08FZ, 06YY and 00Y0; the relocalization paragraph of
lem-sf-clopen-derived-compatibility
(blueprint: lem-sf-clopen-preserves-residue-tor).

Proof: Use the exponent-one derived scalar comparison to identify the local reduction
of the restricted object with restriction of its global reduction. For any local
site object V, compose V to U and U to T. Relocalization identifies the slice of
the local site at V with the slice of the global site at that same composite
object: an object over V is just its weakly etale morphism to V in either case.
Under this site equivalence, the finite coefficient rings are identified by
d.finite 0; d.projection gives the scalar-extension identification. Consequently
slice restriction of the local reduction is the image of slice restriction of
the global reduction under this exact ringed-site equivalence. Every degree-zero
module on the local slice corresponds to a module on the global slice. The
equivalence preserves sheaf tensor products by the balanced pure-tensor formula,
and K-flat resolutions by exactness of its inverse, so it preserves the derived
tensor with these degree-zero modules. It also preserves and reflects zero
cohomology. Apply the assumed global objectwise Tor bound at the composite V to
all these corresponding modules. The ordered-interval conjunct is inherited from
the global test at the same V.
The same cohomology groups vanish outside [a,b], so the integers are unchanged.
For a>b the ordered-interval conjunct makes the premise impossible; empty components
satisfy the same argument. -/
theorem sf_clopen_preserves_residue_tor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    ∀ (M : DerivedCategory (scalarReductionSource l E T)) (a b : ℤ),
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) T
      ((scalarReductionDerivedExtension l E T 0).obj M) a b →
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) U.toScheme
      ((scalarReductionDerivedExtension l E U.toScheme 0).obj
        ((sfClopenDerivedRestriction d).obj M)) a b := by
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralCoefficientAbSheafify.{t, u} U.toScheme
  let := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  obtain ⟨reduction, _, _, _⟩ := sf_clopen_scalar_quotient_comparison l E T U hU d
  intro M a b hM V
  have hfinite := clopenFinite_preservesTor l E T U d
    ((scalarReductionDerivedExtension l E T 0).obj M) a b hM
  let : HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((integralCoefficientSheaf l E U.toScheme 0).over V)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose ((Scheme.ProEt.topology U.toScheme).over V)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((integralCoefficientCommRingSheaf l E U.toScheme 0).over V))) :=
    HasDerivedCategory.standard _
  exact torAmplitude_iso ((integralCoefficientCommRingSheaf l E U.toScheme 0).over V)
    ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
      (integralCoefficientSheaf l E U.toScheme 0) V).mapIso ((reduction 0).app M))
    a b (hfinite V)

end WeilConjectures
