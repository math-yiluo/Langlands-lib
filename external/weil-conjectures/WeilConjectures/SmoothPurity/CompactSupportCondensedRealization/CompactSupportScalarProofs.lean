/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearOpenRestrictionSupport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Generic support, resolution, and derived-mate proofs

Proved categorical subarguments for compact-support coefficient transport.
Sources: Stacks 03EK and 0D6E; blueprint theorem-smooth-purity-all-admissible-coefficients, Step 10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CompactSupportCondensedRealization
attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q DerivedCategory.Qh
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftAdjoint constantSheaf
section OrdinaryOpenComparison
open SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)

private theorem ordinary_coefficient_map_forget_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f) = VaryingRing.ringMap C τ f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
    (eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 U.unop.1 U.unop.2))

private theorem ordinary_push_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push C τ f = VaryingRing.push C τ f := by
  unfold push VaryingRing.push
  rw [ordinary_coefficient_map_forget_eq]

private theorem ordinary_pull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull C τ f = VaryingRing.pull C τ f := by
  unfold pull VaryingRing.pull
  congr 1
  exact ordinary_push_eq C τ f

end OrdinaryOpenComparison

private theorem chosen_unit_isIso_congr
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G)
    (hi : IsIso (Adjunction.ofIsRightAdjoint G).unit) :
    IsIso (Adjunction.ofIsRightAdjoint F).unit := by
  subst G
  exact hi

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- An inverse mate is invertible when its unit and relevant counits are invertible.
Source: Stacks 03EK and 0D6E; blueprint theorem-smooth-purity-all-admissible-coefficients, Step 10.
(blueprint: lem-pur-inverse-mate-supported-counit).
Proof: Expand the inverse mate through its unit and counit. Each factor is an isomorphism, so
every component and hence the natural transformation is invertible. -/
theorem inverse_mate_isIso_of_support
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : R ⋙ F ≅ G ⋙ r) [IsIso a.unit]
    (hc : ∀ M, IsIso (b.counit.app (G.obj (L.obj M)))) :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)) := by
  have hi (M : A) : IsIso
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).app M) := by
    have : IsIso (a.unit.app M) := inferInstance
    have : IsIso (b.counit.app (G.obj (L.obj M))) := hc M
    change IsIso (𝟙 _ ≫ l.map (F.map (a.unit.app M)) ≫
      𝟙 _ ≫ l.map (𝟙 _) ≫ l.map (e.hom.app (L.obj M)) ≫
      l.map (𝟙 _) ≫ 𝟙 _ ≫ b.counit.app (G.obj (L.obj M)) ≫ 𝟙 _)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

section ExactSupport
universe a b c va vb vc w

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
private theorem exact_support_counit_isIso
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : C ⥤ B) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (hc : ∀ N, IsIso (adj.counit.app (S.obj N))) (M : DerivedCategory C) :
    IsIso (adj.mapExactDerivedCategory.counit.app (S.mapDerivedCategory.obj M)) := by
  let d := adj.mapExactDerivedCategory
  have hQ (K : CochainComplex C ℤ) :
      IsIso (d.counit.app (DerivedCategory.Q.obj
        ((S.mapHomologicalComplex (.up ℤ)).obj K))) := by
    let T := (S.mapHomologicalComplex (.up ℤ)).obj K
    have hi (n : ℤ) : IsIso
        (((adj.mapHomologicalComplex (.up ℤ)).counit.app T).f n) := by
      rw [Adjunction.mapHomologicalComplex_counit_app_f]
      change IsIso (adj.counit.app (S.obj (K.X n)))
      exact hc (K.X n)
    have := HomologicalComplex.Hom.isIso_of_components
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app T)
    have he : d.counit.app (DerivedCategory.Q.obj T) =
        L.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app T) ≫
          L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj T) ≫
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app T) := by
      simp only [d, Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
      rfl
    rw [he]
    infer_instance
  have hK (K : CochainComplex C ℤ) :
      IsIso (d.counit.app (S.mapDerivedCategory.obj (DerivedCategory.Q.obj K))) := by
    exact (NatTrans.isIso_app_iff_of_iso d.counit
      (S.mapDerivedCategoryFactors.app K)).mpr (hQ K)
  exact (NatTrans.isIso_app_iff_of_iso d.counit
    (S.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M))).mp (hK _)

end ExactSupport

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- Scalar restriction preserves the derived essential image of open extension.
Source: Stacks 03EK and 0D6E; blueprint theorem-smooth-purity-all-admissible-coefficients, Step 10.
(blueprint: lem-pur-derived-scalar-open-support).
Proof: The ordinary open unit is invertible. The ordinary support theorem makes its counit
invertible on scalar-restricted extensions. Transport that counit through exact derived functors
and use the open derived adjunction to recognize essential-image membership. -/
theorem scalarRestriction_openSupported
    (C D : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (σ : ∀ n, D (n + 1) ⟶ D n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : SemilinearProperOpen.ringSystem C τ X ⟶ SemilinearProperOpen.ringSystem D σ X)
    (M : SemilinearProperOpen.Derived D σ U) :
    (SemilinearProperOpen.J C τ j).essImage
      ((SemilinearSections.res a).mapDerivedCategory.obj
        ((SemilinearProperOpen.J D σ j).obj M)) := by
  have : (VaryingRing.pull C τ j).IsRightAdjoint :=
    VaryingRing.pull_isRightAdjoint C τ j
  have hu : IsIso (SemilinearProperOpen.ordinaryOpenAdj C τ j).unit :=
    chosen_unit_isIso_congr (SemilinearProperOpen.pull C τ j) (VaryingRing.pull C τ j)
      (ordinary_pull_eq C τ j) (VaryingRing.moduleJAdj_unit_isIso C τ j)
  let ff := (SemilinearProperOpen.ordinaryOpenAdj C τ j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hc (N : SemilinearProperOpen.Modules D σ U) :
      IsIso ((SemilinearProperOpen.ordinaryOpenAdj C τ j).counit.app
        ((SemilinearSections.res a).obj ((SemilinearProperOpen.extension D σ j).obj N))) :=
    (SemilinearProperOpen.ordinaryOpenAdj C τ j).isIso_counit_app_iff_mem_essImage.mpr
      (SemilinearProperOpen.scalarRestriction_ordinaryOpenSupported C D τ σ j a N)
  have : PreservesFiniteLimits
      (SemilinearProperOpen.extension D σ j ⋙ SemilinearSections.res a) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (SemilinearProperOpen.extension D σ j ⋙ SemilinearSections.res a) :=
    comp_preservesFiniteColimits _ _
  have hd := exact_support_counit_isIso (SemilinearProperOpen.ordinaryOpenAdj C τ j)
    (SemilinearProperOpen.extension D σ j ⋙ SemilinearSections.res a) hc M
  have := SemilinearProperOpen.jAdj_unit_isIso C τ j
  let ffD := (SemilinearProperOpen.jAdj C τ j).fullyFaithfulLOfIsIsoUnit
  have := ffD.full
  have := ffD.faithful
  apply (SemilinearProperOpen.jAdj C τ j).isIso_counit_app_iff_mem_essImage.mp
  exact (NatTrans.isIso_app_iff_of_iso
    (SemilinearProperOpen.jAdj C τ j).counit
    ((Functor.mapDerivedCategoryCompIso (SemilinearProperOpen.extension D σ j)
      (SemilinearSections.res a)).symm.app M)).mp hd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Continuous module pushforward is additive on morphisms.
Source: the sectionwise module direct-image construction, Stacks 03EK.
(blueprint: lem-pur-scalar-site-pushforward-additive).
Proof: the pushforward maps linear morphisms on each section by the original maps;
therefore addition of two morphisms is preserved on every section. -/
theorem scalarSitePushforward_additive
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous JC JD]
    {R : Sheaf JD RingCat.{u + 1}} {S : Sheaf JC RingCat.{u + 1}}
    (b : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} JC JD).obj R) :
    (SheafOfModules.pushforward.{u + 1} b).Additive := by
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  rfl

attribute [local instance] scalarSitePushforward_additive

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
private theorem equivalence_exact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (e : C ≌ D) :
    e.functor.Additive ∧ PreservesFiniteLimits e.functor ∧
      PreservesFiniteColimits e.functor := by
  let : PreservesLimits e.functor := e.symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesColimits e.functor := e.toAdjunction.leftAdjoint_preservesColimits
  exact ⟨e.functor.additive_of_preserves_binary_products, inferInstance, inferInstance⟩

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
private theorem equivalence_preserves_kInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (e : C ≌ D) [e.functor.Additive] : e.functor.PreservesKInjectiveComplexes := by
  have h := equivalence_exact e.symm
  let := h.1
  let := h.2.1
  let := h.2.2
  exact e.symm.toAdjunction.preservesKInjectiveComplexes

private theorem equivalence_functor_continuous
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u + 1} D]
    (e : C ≌ D) (F : C ⥤ D) (G : D ⥤ C)
    (hF : e.functor = F) (hG : e.inverse = G) (J : GrothendieckTopology C) :
    F.IsContinuous J (G.inducedTopology J) := by
  subst F G
  infer_instance

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A continuous flat site direct image preserves the scalar-restricted injective resolution used
for coefficient transport.
Source: Stacks 03EK and 0D6E; blueprint theorem-smooth-purity-all-admissible-coefficients, Step 10.
(blueprint: lem-pur-continuous-scalar-resolution).
Proof: Pass both sites to their small equivalent models. Construct the ringed direct-image models
and the sectionwise identity comparison isomorphisms. Equivalences are exact and preserve
K-injective complexes; apply the existing ringed resolution theorem and transport the resulting
quasi-isomorphism back through the equivalences. -/
theorem continuous_scalar_resolution
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasSheafify JC AddCommGrpCat.{u + 1}] [HasSheafify JD AddCommGrpCat.{u + 1}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [JC.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (F : C ⥤ D) [F.IsContinuous JC JD] [RepresentablyFlat F]
    (S R : Sheaf JD CommRingCat.{u + 1}) (T : Sheaf JC CommRingCat.{u + 1})
    (a : R ⟶ S) (b : T ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} JC JD).obj R)
    (I : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) ℤ) [I.IsKInjective]
    (J : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ) [J.IsKInjective]
    (j : ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((SheafOfModules.pushforward.{u + 1} (F := F) (J := JC) (K := JD)
      (R := (sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (S := (sheafCompose JC (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)
      ((sheafCompose JC (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)).mapHomologicalComplex
        (.up ℤ)).map j) := by
  let KC := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology JC
  let KD := (AsSmall.down : AsSmall.{u + 1} D ⥤ D).inducedTopology JD
  have : (AsSmall.up : D ⥤ AsSmall.{u + 1} D).IsContinuous JD KD :=
    equivalence_functor_continuous (AsSmall.equiv.{u, u + 1, u + 1} (C := D))
      AsSmall.up AsSmall.down rfl rfl JD
  let G : AsSmall.{u + 1} C ⥤ AsSmall.{u + 1} D :=
    AsSmall.down ⋙ F ⋙ AsSmall.up
  have := Functor.isContinuous_comp F (AsSmall.up : D ⥤ AsSmall.{u + 1} D) JC JD KD
  have : G.IsContinuous KC KD :=
    Functor.isContinuous_comp AsSmall.down (F ⋙ AsSmall.up) KC JC KD
  have : (AsSmall.down : AsSmall.{u + 1} C ⥤ C).IsEquivalence :=
    Equivalence.isEquivalence_inverse (AsSmall.equiv.{u, u + 1, u + 1} (C := C))
  have : (AsSmall.up : D ⥤ AsSmall.{u + 1} D).IsEquivalence :=
    Equivalence.isEquivalence_functor (AsSmall.equiv.{u, u + 1, u + 1} (C := D))
  have : RepresentablyFlat G := by dsimp only [G]; infer_instance
  let L := Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) KC KD
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G (Type (u + 1)) KC KD
  let UC := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).sheafPushforwardContinuous
    CommRingCat.{u + 1} KC JC
  let UD := (AsSmall.down : AsSmall.{u + 1} D ⥤ D).sheafPushforwardContinuous
    CommRingCat.{u + 1} KD JD
  let Sm := UD.obj S
  let Rm := UD.obj R
  let Tm := UC.obj T
  let bm : Tm ⟶ (G.sheafPushforwardContinuous CommRingCat KC KD).obj Rm :=
    ⟨Functor.whiskerLeft AsSmall.down.op b.hom⟩
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists G L adj Rm Tm bm
  let am := (sheafCompose KD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (UD.map a)
  obtain ⟨r, hr⟩ := restrictionRingedToposModuleDirectImage_exists am
  let eS := (VaryingRing.smallModelEquivalence JD
    ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).symm
  let eR := (VaryingRing.smallModelEquivalence JD
    ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).symm
  let eT := (VaryingRing.smallModelEquivalence JC
    ((sheafCompose JC (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)).symm
  let ES := eS.functor
  let ER := eR.functor
  let ET := eT.functor
  have : ES.IsEquivalence := Equivalence.isEquivalence_functor eS
  have : ER.IsEquivalence := Equivalence.isEquivalence_functor eR
  have : ET.IsEquivalence := Equivalence.isEquivalence_functor eT
  have hES := equivalence_exact eS
  have hER := equivalence_exact eR
  have hET := equivalence_exact eT
  have : ES.Additive := hES.1
  have : ER.Additive := hER.1
  have : ET.Additive := hET.1
  have : PreservesFiniteLimits ER := hER.2.1
  have : PreservesFiniteColimits ER := hER.2.2
  have : ER.PreservesHomology := inferInstance
  have : PreservesFiniteLimits ET := hET.2.1
  have : PreservesFiniteColimits ET := hET.2.2
  have : ET.PreservesHomology := inferInstance
  have : ET.ReflectsIsomorphisms := inferInstance
  have : ES.PreservesKInjectiveComplexes := equivalence_preserves_kInjective eS
  have : ER.PreservesKInjectiveComplexes := equivalence_preserves_kInjective eR
  let H := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
  let P := SheafOfModules.pushforward.{u + 1} (F := F) (J := JC) (K := JD)
      (R := (sheafCompose JD (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (S := (sheafCompose JC (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)
    ((sheafCompose JC (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b)
  have : H.Additive := by
    constructor
    intro M N f g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl
  have : P.Additive := scalarSitePushforward_additive F _
  have : r.modules.Additive := r.additive
  have : p.modules.Additive := p.additive
  let α : ES ⋙ r.modules ≅ H ⋙ ER := by
    rw [hr]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by
          intro V V' g
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        ext x
        rfl)
  let β : ER ⋙ p.modules ≅ P ⋙ ET := by
    rw [hp]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by
          intro V V' g
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        ext x
        rfl)
  exact quasiIso_map_of_models ES ER ET r.modules p.modules H P α β
    (ringed_resolution KD KD KC Sm Rm Tm r p) I J j

attribute [-instance] scalarSitePushforward_additive

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open CategoryTheory.Functor in
private theorem derived_square_symm_hom
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategorySquareIso q.symm).hom = (mapDerivedCategorySquareIso q).inv := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryNatIso_symm, Category.assoc]

section ResolvedMateCriterion
attribute [local semireducible] DerivedCategory.Q DerivedCategory.Qh

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem resolved_derived_mate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    [IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom))]
    (hres : ∀ I : CochainComplex B ℤ, I.IsKInjective →
      ∀ J : CochainComplex D ℤ, J.IsKInjective →
      ∀ j : (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
        QuasiIso j → QuasiIso ((R'.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)) := by
  let m := (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom))
  change IsIso m
  have hI (I : CochainComplex B ℤ) [I.IsKInjective] :
      IsIso (m.app (_root_.DerivedCategory.Q.obj I)) := by
    obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((H.mapHomologicalComplex (.up ℤ)).obj I)
    have : J.IsKInjective := hJ
    have : QuasiIso j := hj
    have : QuasiIso ((R'.mapHomologicalComplex (.up ℤ)).map j) :=
      hres I inferInstance J inferInstance j inferInstance
    have hrestricted : IsIso (chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I)) :=
      chainDerivedUnit_isIso_of_resolution R' _ J j
    have hinjective : IsIso (chainDerivedUnit R I) := chainDerivedUnit_isIso R I
    have hchainmate : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app I) := by
      change IsIso (((NatIso.mapHomologicalComplex
        (asIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)))
        (.up ℤ)).app I).hom)
      infer_instance
    have hi : G.mapDerivedCategory.map (chainDerivedUnit R I) ≫
        m.app (_root_.DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) = _ :=
      derived_mate_factors adj adj' s I
    have : IsIso (G.mapDerivedCategory.map (chainDerivedUnit R I) ≫
        m.app (_root_.DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      rw [hi]
      exact (G.mapDerivedCategoryFactors.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≪≫
        (DerivedCategory.Q (C := C)).mapIso (@asIso _ _ _ _ ((NatTrans.mapHomologicalComplex
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app I)
            hchainmate) ≪≫
        @asIso _ _ _ _ (chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I))
          hrestricted).isIso_hom
    have : IsIso (m.app (_root_.DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) :=
      IsIso.of_isIso_comp_left (G.mapDerivedCategory.map (chainDerivedUnit R I)) _
    exact IsIso.of_isIso_comp_right _
      (R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  have (K : _root_.DerivedCategory B) : IsIso (m.app K) := by
    obtain ⟨I, hInj, ⟨eI⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    have : I.IsKInjective := hInj
    have : IsIso (m.app (_root_.DerivedCategory.Q.obj I)) := hI I
    have hn := m.naturality eI.hom
    have : IsIso (m.app K ≫ (H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map eI.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map eI.hom)
  exact NatIso.isIso_of_isIso_app m

end ResolvedMateCriterion

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A derived mate is invertible when the ordinary mate is invertible and restricted resolutions
remain quasi-isomorphisms.
Source: Stacks 03EK and 0D6E; blueprint theorem-smooth-purity-all-admissible-coefficients, Step 10.
(blueprint: lem-pur-derived-mate-resolution-criterion).
Proof: Resolve the scalar-restricted image of each K-injective complex. The resolution condition
makes the target derived unit invertible, and the source unit is invertible on K-injectives. The
derived-mate factorization and ordinary mate then make the derived component invertible. Transport
by naturality from injective representatives to every object; finally identify the inverse of the
symmetrized derived square with the original square. -/
theorem derived_mate_isIso_of_resolution
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    [IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom))]
    (hres : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
      ∀ (J : CochainComplex D ℤ), J.IsKInjective →
      ∀ j : (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
      QuasiIso j → QuasiIso ((R'.mapHomologicalComplex (.up ℤ)).map j)) :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso s.symm).inv)) := by
  rw [← derived_square_symm_hom s.symm]
  exact resolved_derived_mate_isIso adj adj' s hres

end WeilConjectures.CompactSupportCondensedRealization
