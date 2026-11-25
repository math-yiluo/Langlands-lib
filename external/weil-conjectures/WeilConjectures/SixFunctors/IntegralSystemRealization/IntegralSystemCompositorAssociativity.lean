/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence

/-! # Associativity of the section-normalized system pullback compositors

Source: Stacks 03D8, 07A7; the composition calculation in the blueprint
(blueprint: lem-sf-integral-system-compositor-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {o : Operations l E} (c : Compositors l E o)

private theorem direct_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : Y.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f).obj M).val.obj (op (n, U))) :
    ((eqToIso (congrArg (pullbackTensorSequenceDirect l E) e)).hom.app M).val.app
      (op (n, U)) x = M.val.map
        (eqToHom (by cases e; rfl)) x := by
  cases e
  simp

private theorem direct_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : coefficientSequenceModules l E X} (a : M ⟶ N) (n : ℕ) (U : Y.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f).obj M).val.obj (op (n, U))) :
    (((pullbackTensorSequenceDirect l E f).map a).val.app (op (n, U))) x =
      a.val.app (op (n, (proEtaleBaseChange f).obj U)) x := by
  rfl

private theorem direct_obj_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (x : ((pullbackTensorSequenceDirect l E f).obj M).val.obj (op (n, V))) :
    (((pullbackTensorSequenceDirect l E f).obj M).val.map (Prod.mkHom (𝟙 n) a).op) x =
      M.val.map (Prod.mkHom (𝟙 n) ((proEtaleBaseChange f).map a)).op x := by
  rfl

private theorem direct_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (pullbackTensorSequenceDirect l E f) (c.ordinaryDirect g h) ≪≫
        c.ordinaryDirect f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (c.ordinaryDirect f g) (pullbackTensorSequenceDirect l E h) ≪≫
        c.ordinaryDirect (f ≫ g) h ≪≫
        eqToIso (congrArg (pullbackTensorSequenceDirect l E) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_apply l E h ((c.ordinaryDirect f g).hom.app M) n U]
  erw [c.sections f g M n ((proEtaleBaseChange h).obj U)]
  erw [c.sections (f ≫ g) h M n U]
  conv_rhs => erw [direct_transport l E (Category.assoc f g h) M n U]
  conv_lhs => erw [c.sections g h ((pullbackTensorSequenceDirect l E f).obj M) n U x]
  conv_lhs => erw [c.sections f (g ≫ h) M n U]
  conv_lhs => erw [direct_obj_map_apply l E f M n
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U)]
  apply ProEtale.StrictTower.restriction_pasting M.val _ _ _ _ _ _ x
  apply Prod.hom_ext
  · rfl
  · exact ProEtale.StrictTower.site_pasting (P := @WeaklyEtale) (Q := ⊤) f g h U

private theorem ordinaryPull_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.ordinaryPull f g =
      (Adjunction.leftAdjointCompIso (pullbackTensorSequenceAdjunction l E g)
        (pullbackTensorSequenceAdjunction l E f)
        (pullbackTensorSequenceAdjunction l E (f ≫ g)) (c.ordinaryDirect f g)).symm := by
  apply Iso.ext
  change (c.ordinaryPull f g).hom =
    (conjugateEquiv
      ((pullbackTensorSequenceAdjunction l E g).comp
        (pullbackTensorSequenceAdjunction l E f))
      (pullbackTensorSequenceAdjunction l E (f ≫ g))).symm (c.ordinaryDirect f g).hom
  apply (conjugateEquiv
    ((pullbackTensorSequenceAdjunction l E g).comp (pullbackTensorSequenceAdjunction l E f))
    (pullbackTensorSequenceAdjunction l E (f ≫ g))).injective
  rw [Equiv.apply_symm_apply]
  exact congrArg Iso.hom (c.conjugate f g)

private theorem ordinaryPull_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    c.ordinaryPull f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (c.ordinaryPull g h) (pullbackTensorSequenceInverse l E f) =
      eqToIso (congrArg (pullbackTensorSequenceInverse l E) (Category.assoc f g h).symm) ≪≫
        c.ordinaryPull (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (pullbackTensorSequenceInverse l E h) (c.ordinaryPull f g) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (pullbackTensorSequenceAdjunction l E h) (pullbackTensorSequenceAdjunction l E g)
    (pullbackTensorSequenceAdjunction l E f)
    (pullbackTensorSequenceAdjunction l E (g ≫ h))
    (pullbackTensorSequenceAdjunction l E (f ≫ g))
    (pullbackTensorSequenceAdjunction l E (f ≫ g ≫ h))
    (c.ordinaryDirect g h) (c.ordinaryDirect f g)
    (c.ordinaryDirect (f ≫ g) h ≪≫
      eqToIso (congrArg (pullbackTensorSequenceDirect l E) (Category.assoc f g h)))
    (c.ordinaryDirect f (g ≫ h)) (direct_assoc l E c f g h)
  have ht := ProEtale.StrictTower.mate_transport (pullbackTensorSequenceInverse l E)
    (pullbackTensorSequenceDirect l E) (fun f ↦ pullbackTensorSequenceAdjunction l E f)
    (pullbackTensorSequenceAdjunction l E h)
    (pullbackTensorSequenceAdjunction l E (f ≫ g))
    (Category.assoc f g h) (c.ordinaryDirect (f ≫ g) h)
  rw [ht] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hi := congr_app (congrArg Iso.inv hh) M
  simpa only [ordinaryPull_eq, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Iso.symm_inv, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Category.id_comp, Category.comp_id, Category.assoc,
    eqToIso.inv, eqToIso.hom] using hi.symm

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryFactors

private theorem derived_comp_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (d : H.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (hd : ∀ P : CochainComplex C ℤ,
      d.hom.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        H.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) :
    d = Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
  intro P
  apply (cancel_mono (G.mapDerivedCategory.map
    (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hd]
  have hc := Functor.mapDerivedCategoryCompIso_fac F G P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
    ext n
    rfl
  erw [hi, DerivedCategory.Q.map_id, Category.comp_id] at hc
  rw [hc, Functor.mapDerivedCategoryNatIso_fac]
  rfl

private theorem pullComp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.pullComp f g = Functor.mapDerivedCategoryNatIso (c.ordinaryPull f g) ≪≫
      (Functor.mapDerivedCategoryCompIso (pullbackTensorSequenceInverse l E g)
        (pullbackTensorSequenceInverse l E f)).symm := by
  exact derived_comp_eq (pullbackTensorSequenceInverse l E g)
    (pullbackTensorSequenceInverse l E f) (pullbackTensorSequenceInverse l E (f ≫ g))
    (c.ordinaryPull f g) (c.pullComp f g) (c.pullComp_model f g)

private theorem derived_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (pullbackTensorSequenceInverse l E) e))).hom =
      (eqToIso (congrArg (pull l E) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The recorded system pullback compositors satisfy associativity.
Source: Stacks 03D8 and 07A7
(blueprint: lem-sf-integral-system-compositor-associativity).

Proof: both ordinary direct-image composites restrict sections along the same map
between the triple fibre products. Conjugation transfers this equality to the ordinary
inverse images. The recorded complex-factor equation identifies each derived compositor
with localization of that ordinary comparison. Exact localization preserves the equality.
This proves an equality in the full system category, with every coefficient transition.
-/
theorem integralSystemCompositorAssociativity {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    c.pullComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c.pullComp g h) (pull l E f) =
      eqToIso (congrArg (pull l E) (Category.assoc f g h).symm) ≪≫
        c.pullComp (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (pull l E h) (c.pullComp f g) := by
  have hh := ProEtale.StrictTower.descend_coherence
    (pullbackTensorSequenceInverse l E h) (pullbackTensorSequenceInverse l E g)
    (pullbackTensorSequenceInverse l E f) (pullbackTensorSequenceInverse l E (g ≫ h))
    (pullbackTensorSequenceInverse l E (f ≫ g))
    (pullbackTensorSequenceInverse l E (f ≫ g ≫ h))
    (pullbackTensorSequenceInverse l E ((f ≫ g) ≫ h))
    (c.ordinaryPull g h) (c.ordinaryPull f g)
    (c.ordinaryPull f (g ≫ h)) (c.ordinaryPull (f ≫ g) h)
    (eqToIso (congrArg (pullbackTensorSequenceInverse l E) (Category.assoc f g h).symm))
    (ordinaryPull_assoc l E c f g h)
  rw [derived_transport l E (Category.assoc f g h).symm] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [pullComp_eq, pull, pullbackTensorSequenceDerived, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Functor.map_comp] using congr_app hh M

end WeilConjectures.IntegralSystemRealization
