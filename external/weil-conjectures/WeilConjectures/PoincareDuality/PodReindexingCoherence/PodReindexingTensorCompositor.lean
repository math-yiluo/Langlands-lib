/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import Mathlib.Tactic.CategoryTheory.Slice
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Tensor normalization of the reindexing composition

Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI.
(blueprint: lem-pod-reindexing-tensor-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  podReindexingCoefficient coefficientTotalTensor coefficientTensorGenerator
  HasDerivedCategory.standard

private local instance (priority := 1000002) coefficientSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} W

private local instance (priority := 1000002) coefficientWeakSheafify (W : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  HasSheafify.isRightAdjoint

set_option linter.defProp false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
@[instance_reducible]
private def cachedCompose (W : Scheme.{u}) :
    (ProEt.topology W).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  hasSheafCompose_of_preservesLimitsOfSize (F :=
    forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) (ProEt.topology W)

attribute [local instance 1000001] cachedCompose

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private def ringCoefficient {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ) :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (podReindexingRing l E Y s)) ≅
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (podReindexingRing l E X s) :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (podReindexingCoefficient l E g s)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem ringCoefficient_finite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) : (ringCoefficient l E g (some n)).hom =
      isoSectionwiseConstantMap.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  simpa only [ringCoefficient, podReindexingCoefficient, Functor.mapIso_hom] using
    (podReindexingCoefficient_existsUnique l E g).exists.choose_spec.1 n

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem ringCoefficient_projection {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) : (ringCoefficient l E g none).hom ≫
        limit.π (integralCoefficientSheafSystem l E X) (op n) =
      (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
          (ringCoefficient l E g (some n)).hom := by
  have hn := congrArg
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
    ((podReindexingCoefficient_existsUnique l E g).exists.choose_spec.2 n)
  simp only [ringCoefficient, podReindexingCoefficient, Functor.mapIso_hom]
  with_unfolding_all exact hn

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private def sectionComposition {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
    [IsIso h] [IsIso f] (D : Type*) [Category D] :
    isoSectionwiseInverseImage (h ≫ f) D ≅
      isoSectionwiseInverseImage f D ⋙ isoSectionwiseInverseImage h D :=
  (Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).symm
    D (ProEt.topology Z) (ProEt.topology W) (ProEt.topology V)).symm

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem constantComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] (R : CommRingCat.{u + 1}) :
    isoSectionwiseConstantMap.{u, u} (h ≫ f) R =
      (sectionComposition h f RingCat.{u + 1}).hom.app
          ((sheafCompose (ProEt.topology V)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj R)) ≫
        (isoSectionwiseInverseImage h RingCat).map (isoSectionwiseConstantMap.{u, u} f R) ≫
          isoSectionwiseConstantMap.{u, u} h R := by
  apply (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ f) R).unique
    (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ f) R).exists.choose_spec
  intro U a
  change (isoSectionwiseConstantMap.{u, u} h R).hom.app (op U)
    ((isoSectionwiseConstantMap.{u, u} f R).hom.app (op ((proEtaleIsoPostcompose h).obj U))
      (((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj R).obj.map
        ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op
        ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
          (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) a))) = _
  have hn :
      ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj R).obj.map
          ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op
          ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
            (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) a) =
        (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).app
          (op ((proEtaleIsoPostcompose f).obj ((proEtaleIsoPostcompose h).obj U))) a :=
    congrArg (fun q ↦ q a)
      ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj R)).naturality
        ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op).symm
  erw [hn]
  erw [show (isoSectionwiseConstantMap.{u, u} f R).hom.app
      (op ((proEtaleIsoPostcompose h).obj U)) _ = _ from
    (isoSectionwiseConstantMap_existsUnique.{u, u} f R).exists.choose_spec
      ((proEtaleIsoPostcompose h).obj U) a]
  exact (isoSectionwiseConstantMap_existsUnique.{u, u} h R).exists.choose_spec U a

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem coefficientComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] (s : Option ℕ) :
    (ringCoefficient l E (h ≫ f) s).hom =
      (sectionComposition h f RingCat.{u + 1}).hom.app
          ((sheafCompose (ProEt.topology V)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (podReindexingRing l E V s)) ≫
        (isoSectionwiseInverseImage h RingCat).map (ringCoefficient l E f s).hom ≫
          (ringCoefficient l E h s).hom := by
  cases s with
  | some n =>
    simp only [ringCoefficient_finite]
    exact constantComposition h f _
  | none =>
    apply limit.hom_ext
    intro n
    let H := isoSectionwiseInverseImage h RingCat.{u + 1}
    let HF := isoSectionwiseInverseImage (h ≫ f) RingCat.{u + 1}
    let a := sectionComposition h f RingCat.{u + 1}
    have hh := ringCoefficient_projection l E h n.unop
    have hf := ringCoefficient_projection l E f n.unop
    have hhf := ringCoefficient_projection l E (h ≫ f) n.unop
    erw [hhf, ringCoefficient_finite, constantComposition]
    change HF.map _ ≫ (a.hom.app _ ≫ H.map _ ≫ _) =
      (a.hom.app _ ≫ H.map _ ≫ _) ≫ _
    rw [Category.assoc, Category.assoc, hh, ← H.map_comp_assoc, hf, H.map_comp]
    simp only [ringCoefficient_finite]
    rw [← Category.assoc, ← Category.assoc, a.hom.naturality]
    simp only [Functor.comp_map, Category.assoc, H]

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private def ordinaryComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] (s : Option ℕ) :
    podReindexingFunctor l E (h ≫ f) s ≅
      podReindexingFunctor l E f s ⋙ podReindexingFunctor l E h s := by
  let H := isoSectionwiseInverseImage h RingCat.{u + 1}
  let e := siteComp f h
  letI : (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose f).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
    Functor.isContinuous_comp (proEtaleIsoPostcompose h) (proEtaleIsoPostcompose f)
      (ProEt.topology Z) (ProEt.topology W) (ProEt.topology V)
  let c := ringCoefficient l E (h ≫ f) s
  let d := H.mapIso (ringCoefficient l E f s) ≪≫ ringCoefficient l E h s
  let a := SheafOfModules.pushforwardNatIso
    (J := ProEt.topology Z) (K := ProEt.topology V)
    (F := proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose f)
    (G := proEtaleIsoPostcompose (h ≫ f)) c.inv e.symm
  let b : podReindexingFunctor l E (h ≫ f) s ≅ SheafOfModules.pushforward c.inv :=
    SheafOfModules.pushforwardCongr (IsIso.inv_eq_of_hom_inv_id c.hom_inv_id)
  refine b ≪≫ a ≪≫ SheafOfModules.pushforwardCongr ?_ ≪≫
    (SheafOfModules.pushforwardComp (inv (ringCoefficient l E h s).hom)
      (inv (ringCoefficient l E f s).hom)).symm
  simp only [IsIso.inv_eq_of_hom_inv_id (ringCoefficient l E h s).hom_inv_id,
    IsIso.inv_eq_of_hom_inv_id (ringCoefficient l E f s).hom_inv_id]
  change c.inv ≫ (sectionComposition h f RingCat.{u + 1}).hom.app _ = d.inv
  apply (cancel_mono d.hom).1
  rw [Category.assoc]
  change c.inv ≫ ((sectionComposition h f RingCat.{u + 1}).hom.app _ ≫
    H.map (ringCoefficient l E f s).hom ≫ (ringCoefficient l E h s).hom) = _
  rw [← coefficientComposition l E h f s, c.inv_hom_id, d.inv_hom_id]

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem ordinaryComposition_sections {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f] (s : Option ℕ)
    (M : podReindexingModules l E V s) (U : Z.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))) :
    HEq (((ordinaryComposition l E h f s).hom.app M).val.app (op U) x)
      (M.val.map ((siteComp f h).inv.app U).op x) := by
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem composition_derived_factors
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G) (K : CochainComplex C₀ ℤ) :
    (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm).hom.app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have ha := Functor.mapDerivedCategoryNatIso_fac a K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  rw [hid] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [hc, ha]
  congr 2
  change _ = (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K ≫ 𝟙 _
  exact (Category.comp_id _).symm

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private def canonicalCompositor {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X)
    [IsIso g] [IsIso h] (s : Option ℕ) : Compositor l E g h s := by
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Z s)
  let a := ordinaryComposition l E h g s
  let ac := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (podReindexingFunctor l E g s ⋙ podReindexingFunctor l E h s))
      (.up ℤ)).symm
  refine
    { ordinary := a
      sections := ordinaryComposition_sections l E h g s
      complex := fun P ↦ ac.app P
      degree := fun P i ↦ ?_
      derived := Functor.mapDerivedCategoryNatIso a ≪≫
        (Functor.mapDerivedCategoryCompIso (podReindexingFunctor l E g s)
          (podReindexingFunctor l E h s)).symm
      model := fun P ↦ ?_ }
  · exact Category.comp_id _
  · exact composition_derived_factors (podReindexingFunctor l E g s)
      (podReindexingFunctor l E h s) (podReindexingFunctor l E (h ≫ g) s) a P

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  CoefficientClosedStructure.tensor SheafOfModules.monoidalCategory
  podReindexingHomModel homComplexFunctor homComplexπ derivedInternalHomOfUniverses

-- Keep the coefficient and site presentations shared during this comparison.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem generator_restrict (W : Scheme.{u})
    [EssentiallySmall.{u + 1} W.ProEt] (s : Option ℕ) (P L : K l E W s)
    (p q n : ℤ) (hpq : p + q = n) {U V : W.ProEtᵒᵖ} (i : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((total l E W s).obj (P, L)).X n).val.map i
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
          (podReindexingRing l E W s) P L p q n hpq U x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
        (podReindexingRing l E W s) P L p q n hpq V
          ((P.X p).val.map i x) ((L.X q).val.map i y) := by
  let R := podReindexingRing l E W s
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let ι := HomologicalComplex.ιMapBifunctor P L (MonoidalCategory.curriedTensor _)
    (.up ℤ) p q n hpq
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat RingCat)).obj R).obj)
  let z := x ⊗ₜ[R.obj.obj U] y
  have hi := PresheafOfModules.naturality_apply ι.val i
    ((SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (L.X q)).inv.val.app U
      ((adj.unit.app ((P.X p).val ⊗ (L.X q).val)).app U z))
  have ht := PresheafOfModules.naturality_apply
    (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (L.X q)).inv.val i
    ((adj.unit.app ((P.X p).val ⊗ (L.X q).val)).app U z)
  have hu := PresheafOfModules.naturality_apply
    (adj.unit.app ((P.X p).val ⊗ (L.X q).val)) i z
  dsimp only [Functor.id_obj] at hu
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at hu
  simp only [coefficientTotalTensor, coefficientTensorGenerator]
  change ((HomologicalComplex.mapBifunctor P L
      (MonoidalCategory.curriedTensor (podReindexingModules l E W s))
      (.up ℤ)).X n).val.map i
      ((ι.val.app U) (((SheafOfModules.tensorObjIsoSheafification
        (R := R) (P.X p) (L.X q)).inv.val.app U)
        ((adj.unit.app ((P.X p).val ⊗ (L.X q).val)).app U z))) = _
  with_unfolding_all
    exact (hi.symm.trans (congrArg (ι.val.app V)
      (ht.symm.trans (congrArg
        ((SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (L.X q)).inv.val.app V)
        hu.symm))))

-- Compose the pure-section equations directly, without rewriting the transported total complexes.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem tensor_chain_square {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [EssentiallySmall.{u + 1} Z.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s) (SZ : Closed l E Z s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) (TZ : Models l E Z s SZ)
    (cg : Comparison l E g s SX SY TX TY) (ch : Comparison l E h s SZ SX TZ TX)
    (cgh : Comparison l E (h ≫ g) s SZ SY TZ TY) (k : Compositor l E g h s)
    (P L : K l E Y s) :
    (cgh.tensorChain P L).hom ≫ (total l E Z s).map
        (Prod.mkHom (k.complex P).hom (k.complex L).hom) =
      (k.complex ((total l E Y s).obj (P, L))).hom ≫
        (podReindexingComplexFunctor l E h s).map (cg.tensorChain P L).hom ≫
          (ch.tensorChain ((podReindexingComplexFunctor l E g s).obj P)
            ((podReindexingComplexFunctor l E g s).obj L)).hom := by
  let c := cgh.tensorChain P L
  apply (cancel_epi c.inv).1
  ext n : 1
  apply ScalarHomTensor.total_pure_hom_ext
    (P := (podReindexingComplexFunctor l E (h ≫ g) s).obj P)
    (Q := (podReindexingComplexFunctor l E (h ≫ g) s).obj L)
    (n := n)
    (J := ProEt.topology Z) (R := podReindexingRing l E Z s)
  intro p q hpq U x y
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) P L p q n hpq
      (op ((proEtaleIsoPostcompose (h ≫ g)).obj U.unop)) x y
  have hcancel := congrArg (fun a ↦ (a.f n).val.app U z)
    (cgh.tensorChain P L).hom_inv_id
  have hi := congrArg
    (fun z ↦ (((cgh.tensorChain P L).inv.f n).val.app U) z)
    (cgh.tensorChain_pure P L p q n hpq U.unop x y)
  have hi' : (((cgh.tensorChain P L).inv.f n).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Z)
        (podReindexingRing l E Z s) ((podReindexingComplexFunctor l E (h ≫ g) s).obj P)
        ((podReindexingComplexFunctor l E (h ≫ g) s).obj L) p q n hpq U x y) = z :=
    hi.symm.trans hcancel
  let m := (((total l E Z s).map
    (Prod.mkHom (k.complex P).hom (k.complex L).hom)).f n).val.app U
  let a := ((k.complex ((total l E Y s).obj (P, L))).hom.f n).val.app U
  let b := ((cg.tensorChain P L).hom.f n).val.app
    (op ((proEtaleIsoPostcompose h).obj U.unop))
  let d := ((ch.tensorChain ((podReindexingComplexFunctor l E g s).obj P)
    ((podReindexingComplexFunctor l E g s).obj L)).hom.f n).val.app U
  let xp := (P.X p).val.map ((siteComp g h).inv.app U.unop).op x
  let yq := (L.X q).val.map ((siteComp g h).inv.app U.unop).op y
  have hx : ((k.complex P).hom.f p).val.app U x = xp :=
    (congrArg (fun m ↦ m.val.app U x) (k.degree P p)).trans
      (eq_of_heq (k.sections (P.X p) U.unop x))
  have hy : ((k.complex L).hom.f q).val.app U y = yq :=
    (congrArg (fun m ↦ m.val.app U y) (k.degree L q)).trans
      (eq_of_heq (k.sections (L.X q) U.unop y))
  have hz : a z = (((total l E Y s).obj (P, L)).X n).val.map
      ((siteComp g h).inv.app U.unop).op z :=
    (congrArg (fun m ↦ m.val.app U z)
      (k.degree ((total l E Y s).obj (P, L)) n)).trans
      (eq_of_heq (k.sections (((total l E Y s).obj (P, L)).X n) U.unop z))
  have hleft := (congrArg (fun v ↦ m v)
    (cgh.tensorChain_pure P L p q n hpq U.unop x y)).trans
      ((ScalarHomTensor.tensor_generator_map (J := ProEt.topology Z)
        (R := podReindexingRing l E Z s) (k.complex P).hom (k.complex L).hom
          p q n hpq U x y).trans
        (congrArg₂ (fun x y ↦ coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Z) (podReindexingRing l E Z s)
          ((podReindexingComplexFunctor l E h s).obj
            ((podReindexingComplexFunctor l E g s).obj P))
          ((podReindexingComplexFunctor l E h s).obj
            ((podReindexingComplexFunctor l E g s).obj L)) p q n hpq U x y) hx hy))
  have hright := (congrArg (fun v ↦ d (b v))
    (hz.trans (generator_restrict l E Y s P L p q n hpq
      ((siteComp g h).inv.app U.unop).op x y))).trans
      ((congrArg (fun v ↦ d v)
        (cg.tensorChain_pure P L p q n hpq
          ((proEtaleIsoPostcompose h).obj U.unop) xp yq)).trans
        (ch.tensorChain_pure ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj L) p q n hpq U.unop xp yq))
  exact (congrArg (fun v ↦ m (((cgh.tensorChain P L).hom.f n).val.app U v)) hi').trans
    (hleft.trans (hright.symm.trans (congrArg (fun v ↦ d (b (a v))) hi').symm))

/-- Paste the representative equations in an abstract category before specializing to sheaves. -/
private theorem tensor_compositor_paste {C : Type*} [Category C]
    {A₀ A B D B' D' T H F G K U V W M N S D₁ : C}
    (u : A₀ ⟶ A) [Epi u] (t : D ⟶ D') [Mono t]
    {c : A ⟶ B} {d : B ⟶ D} {k : A ⟶ V} {g : V ⟶ W} {h : W ⟶ D}
    {a : A₀ ⟶ T} {qH : T ⟶ H} {rH : H ⟶ B'} {vA : B ⟶ B'}
    {vK : B' ⟶ D'} {qT : H ⟶ U} {rZ : U ⟶ D'}
    {qk : T ⟶ K} {qG : K ⟶ S} {qh : S ⟶ U}
    {k₀ : A₀ ⟶ F} {e : F ⟶ G} {f : G ⟶ K} {r : F ⟶ V}
    {vE : D ⟶ D₁} {vF : D₁ ⟶ D'} {gE : W ⟶ N} {h' : N ⟶ D₁}
    {gq : G ⟶ M} {gr : M ⟶ N} {f' : M ⟶ S}
    (hs : d ≫ t = vA ≫ vK)
    (hc : u ≫ c ≫ vA = a ≫ qH ≫ rH)
    (hr : qT ≫ rZ = rH ≫ vK)
    (hchain : qH ≫ qT = qk ≫ qG ≫ qh)
    (hk : k₀ ≫ e ≫ f = a ≫ qk)
    (hnat : u ≫ k = k₀ ≫ r)
    (ht : t = vE ≫ vF)
    (hn : gE ≫ h' = h ≫ vE)
    (ha : r ≫ g ≫ gE = e ≫ gq ≫ gr)
    (hb : gr ≫ h' ≫ vF = f' ≫ qh ≫ rZ)
    (hf : gq ≫ f' = f ≫ qG) :
    c ≫ d = k ≫ g ≫ h := by
  apply (cancel_epi u).1
  apply (cancel_mono t).1
  simp only [Category.assoc]
  slice_lhs 3 4 => exact hs
  slice_lhs 1 3 => exact hc
  simp only [Category.assoc]
  slice_lhs 3 4 => exact hr.symm
  slice_lhs 2 3 => exact hchain
  simp only [Category.assoc]
  slice_lhs 1 2 => exact hk.symm
  simp only [Category.assoc]
  slice_rhs 1 2 => exact hnat
  simp only [Category.assoc]
  rw [ht]
  slice_rhs 4 5 => exact hn.symm
  slice_rhs 2 4 => exact ha
  simp only [Category.assoc]
  slice_rhs 4 6 => exact hb
  slice_rhs 3 4 => exact hf
  simp only [Category.assoc]

-- Paste the three tensor models across the exact-functor factorization maps.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
private theorem tensor_on_representatives {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [EssentiallySmall.{u + 1} Z.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s) (SZ : Closed l E Z s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) (TZ : Models l E Z s SZ)
    (cg : Comparison l E g s SX SY TX TY) (ch : Comparison l E h s SZ SX TZ TX)
    (cgh : Comparison l E (h ≫ g) s SZ SY TZ TY) (k : Compositor l E g h s)
    (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L) :
    cgh.tensor.hom.app ((podReindexingQ l E Y s).obj P,
        (podReindexingQ l E Y s).obj L) ≫ SZ.tensor.map
          (Prod.mkHom (k.derived.hom.app ((podReindexingQ l E Y s).obj P))
            (k.derived.hom.app ((podReindexingQ l E Y s).obj L))) =
      k.derived.hom.app (SY.tensor.obj ((podReindexingQ l E Y s).obj P,
          (podReindexingQ l E Y s).obj L)) ≫
        (podReindexingDerivedFunctor l E h s).map
          (cg.tensor.hom.app ((podReindexingQ l E Y s).obj P,
            (podReindexingQ l E Y s).obj L)) ≫
          ch.tensor.hom.app ((podReindexingDerivedFunctor l E g s).obj
            ((podReindexingQ l E Y s).obj P), (podReindexingDerivedFunctor l E g s).obj
              ((podReindexingQ l E Y s).obj L)) := by
  let F := podReindexingDerivedFunctor l E g s
  let G := podReindexingDerivedFunctor l E h s
  let H := podReindexingDerivedFunctor l E (h ≫ g) s
  let Fc := podReindexingComplexFunctor l E g s
  let Gc := podReindexingComplexFunctor l E h s
  let Hc := podReindexingComplexFunctor l E (h ≫ g) s
  let QY := podReindexingQ l E Y s
  let QZ := podReindexingQ l E Z s
  let e := podReindexingDerivedFactors l E g s
  let f := podReindexingDerivedFactors l E h s
  let a := podReindexingDerivedFactors l E (h ≫ g) s
  let V := SZ.tensor
  obtain ⟨hFP, hFL, ha⟩ := cg.tensor_model P L hP hL
  obtain ⟨hGFP, hGFL, hb⟩ := ch.tensor_model (Fc.obj P) (Fc.obj L) hFP hFL
  obtain ⟨hHP, hHL, hc⟩ := cgh.tensor_model P L hP hL
  let rY := TY.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩)
  let rX := TX.comparison.hom.app (⟨Fc.obj P, hFP⟩, ⟨Fc.obj L, hFL⟩)
  let rZ := TZ.comparison.hom.app (⟨Gc.obj (Fc.obj P), hGFP⟩,
    ⟨Gc.obj (Fc.obj L), hGFL⟩)
  let rH := TZ.comparison.hom.app (⟨Hc.obj P, hHP⟩, ⟨Hc.obj L, hHL⟩)
  let t := V.map (Prod.mkHom
    (G.map (e.hom.app P) ≫ f.hom.app (Fc.obj P))
    (G.map (e.hom.app L) ≫ f.hom.app (Fc.obj L)))
  have ht : IsIso t := by
    change IsIso (V.mapIso
      ((G.mapIso (e.app P) ≪≫ f.app (Fc.obj P)).prod
        (G.mapIso (e.app L) ≪≫ f.app (Fc.obj L)))).hom
    infer_instance
  have ht' : t = V.map (Prod.mkHom (G.map (e.hom.app P)) (G.map (e.hom.app L))) ≫
      V.map (Prod.mkHom (f.hom.app (Fc.obj P)) (f.hom.app (Fc.obj L))) := by
    dsimp only [t]
    rw [← V.map_comp]
    rfl
  have hs : V.map (Prod.mkHom (k.derived.hom.app (QY.obj P))
        (k.derived.hom.app (QY.obj L))) ≫ t =
      V.map (Prod.mkHom (a.hom.app P) (a.hom.app L)) ≫
        V.map (Prod.mkHom (QZ.map (k.complex P).hom) (QZ.map (k.complex L).hom)) := by
    simp only [t, ← V.map_comp]
    apply congrArg V.map
    apply Prod.ext
    · change k.derived.hom.app (QY.obj P) ≫
        (G.map (e.hom.app P) ≫ f.hom.app (Fc.obj P)) = _
      exact k.model P
    · change k.derived.hom.app (QY.obj L) ≫
        (G.map (e.hom.app L) ≫ f.hom.app (Fc.obj L)) = _
      exact k.model L
  have hr : QZ.map ((total l E Z s).map
      (Prod.mkHom (k.complex P).hom (k.complex L).hom)) ≫ rZ =
      rH ≫ V.map (Prod.mkHom (QZ.map (k.complex P).hom)
        (QZ.map (k.complex L).hom)) := by
    exact TZ.comparison.hom.naturality
      (Prod.mkHom
        (ObjectProperty.homMk (X := ⟨Hc.obj P, hHP⟩)
          (Y := ⟨Gc.obj (Fc.obj P), hGFP⟩) (k.complex P).hom)
        (ObjectProperty.homMk (X := ⟨Hc.obj L, hHL⟩)
          (Y := ⟨Gc.obj (Fc.obj L), hGFL⟩) (k.complex L).hom))
  have hn := ch.tensor.hom.naturality (Prod.mkHom (e.hom.app P) (e.hom.app L))
  change G.map (SX.tensor.map (Prod.mkHom (e.hom.app P) (e.hom.app L))) ≫
      ch.tensor.hom.app _ = ch.tensor.hom.app _ ≫
        V.map (Prod.mkHom (G.map (e.hom.app P)) (G.map (e.hom.app L))) at hn
  have hf := f.hom.naturality (cg.tensorChain P L).hom
  change G.map ((podReindexingQ l E X s).map (cg.tensorChain P L).hom) ≫
      f.hom.app _ = f.hom.app _ ≫ QZ.map (Gc.map (cg.tensorChain P L).hom) at hf
  have hga := congrArg G.map ha
  simp only [Functor.map_comp] at hga
  have hchain := congrArg QZ.map (tensor_chain_square l E g h s SX SY SZ TX TY TZ
    cg ch cgh k P L)
  simp only [Functor.map_comp] at hchain
  have hk := k.model ((total l E Y s).obj (P, L))
  have hkNat := k.derived.hom.naturality rY
  change H.map rY ≫ k.derived.hom.app _ =
    k.derived.hom.app _ ≫ G.map (F.map rY) at hkNat
  exact tensor_compositor_paste (H.map rY) t hs hc hr hchain hk hkNat ht' hn hga hb hf

-- The representative argument involves three exact derived functors.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology in
/-- The canonical site and localized tensor composition comparison.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 09A5, 07A4, 0FPI
(blueprint: lem-pod-reindexing-tensor-compositor).

Proof: For a module M and a pro-etale object U of Z, define the ordinary comparison by the
restriction of M along (siteComp g h).inv.app U. Define its inverse using siteComp.hom. The two
composites are identities by functoriality of restriction and the site isomorphism identities.
These section maps commute with restriction by naturality of siteComp. They are linear: the
coefficient restriction along this site map is the identity on the finite-stage constant
coefficients; at the completed stage the same assertion holds after every quotient projection,
which jointly detect equality. Thus these maps assemble to the ordinary natural module isomorphism
and give the required sections field.

For each cochain complex P use this ordinary comparison in degree i. Naturality with respect to
P.d proves commutation with the differential. The degree field is then the defining equation, and
naturality in chain maps is inherited degreewise. Both exact reindexing functors invert quasi-
isomorphisms. Descend this natural chain isomorphism through the localization functor. Whiskering
with the localization is fully faithful, so the descended isomorphism has exactly the model
equation with the three recorded podReindexingDerivedFactors. This constructs every field of
Compositor, without choosing an arbitrary natural isomorphism.

First prove the tensor square on the actual total complexes. In the summand of bidegree (p,q),
both routes send a pure section x tensor y over U to the tensor of their restrictions along
siteComp.inv.app U. This uses the tensorChain_pure fields of cg, ch and cgh; there is no
interchange of degrees and hence no sign. The sheafified pure generators and total-summand
inclusions detect equality, so the chain square follows. Reindexing along a scheme isomorphism
preserves K-flat complexes as already recorded in the tensor_model fields. Apply the three
tensor_model equations to independently K-flat representatives P,Q. Substitute the chain square
and the compositor model equation, and cancel the comparison isomorphisms. This proves the
displayed derived tensor square on Q(P),Q(Q). Finally take independent K-flat resolutions of
arbitrary M,N; naturality of the tensor comparisons and compositor transports that square across
their invertible augmentations. No Hom equation is assumed or asserted here.
-/
theorem tensor_compositor_exists {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [EssentiallySmall.{u + 1} Z.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s) (SZ : Closed l E Z s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) (TZ : Models l E Z s SZ)
    (cg : Comparison l E g s SX SY TX TY) (ch : Comparison l E h s SZ SX TZ TX)
    (cgh : Comparison l E (h ≫ g) s SZ SY TZ TY) :
    ∃ k : Compositor l E g h s,
      (∀ M N : podReindexingDerived l E Y s,
        cgh.tensor.hom.app (M, N) ≫ SZ.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (SY.tensor.obj (M, N)) ≫
          (podReindexingDerivedFunctor l E h s).map (cg.tensor.hom.app (M, N)) ≫
          ch.tensor.hom.app ((podReindexingDerivedFunctor l E g s).obj M,
            (podReindexingDerivedFunctor l E g s).obj N)) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let k := canonicalCompositor l E g h s
  let F := podReindexingDerivedFunctor l E g s
  let G := podReindexingDerivedFunctor l E h s
  let Q := podReindexingQ l E Y s
  let α := cgh.tensor ≪≫
    Functor.isoWhiskerRight (NatIso.prod k.derived k.derived) SZ.tensor
  let β := Functor.isoWhiskerLeft SY.tensor k.derived ≪≫
    Functor.isoWhiskerRight cg.tensor G ≪≫
      Functor.isoWhiskerLeft (F.prod F) ch.tensor
  have hc (P L : K l E Y s)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
      (hL : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L) :
      α.hom.app (Q.obj P, Q.obj L) = β.hom.app (Q.obj P, Q.obj L) :=
    tensor_on_representatives l E g h s SX SY SZ TX TY TZ cg ch cgh k P L hP hL
  have hab : α.hom = β.hom := by
    apply NatTrans.ext
    funext MN
    obtain ⟨M, N⟩ := MN
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage M)
    obtain ⟨L, q, hL, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage N)
    have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
    have : IsIso (Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
    let eM : Q.obj P ≅ M := asIso (Q.map p) ≪≫ Q.objObjPreimageIso M
    let eN : Q.obj L ≅ N := asIso (Q.map q) ≪≫ Q.objObjPreimageIso N
    let e := eM.prod eN
    apply (cancel_epi ((SY.tensor ⋙ podReindexingDerivedFunctor l E (h ≫ g) s).map
      e.hom)).1
    rw [α.hom.naturality e.hom, β.hom.naturality e.hom]
    rw [hc P L hP hL]
    rfl
  refine ⟨k, fun M N ↦ ?_⟩
  exact congrArg (fun z ↦ z.app (M, N)) hab

end WeilConjectures.PodReindexingCoherence
