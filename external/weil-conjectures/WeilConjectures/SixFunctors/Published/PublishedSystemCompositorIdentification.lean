/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Published.PublishedSystemAmbientPresentation

/-! # Normalization of the published system presentation

Source: Stacks 03D3, 03EL, 07A4 and 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
attribute [local implicit_reducible] pullbackTensorSequenceInverse pullbackTensorSequenceDerived
  pullbackTensorSequenceDirect pullbackTensorSequenceBase MorphismProperty Scheme.ProEt
  AmbientPullbackTensor.pull AmbientPullbackTensor.adjunction AmbientPullbackTensor.push
  AmbientPullbackTensor.Site AmbientPullbackTensor.base AmbientPullbackTensor.siteCategory
  AmbientPullbackTensor.topology AmbientPullbackTensor.coefficients
  AmbientPullbackTensor.pushComp AmbientPullbackTensor.comp coefficientSequenceHasDerived
  SemilinearSections.hasDerived SemilinearSections.moduleAbelian

private abbrev ambient_direct {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
  AmbientPullbackTensor.push l E f none

private local instance ambient_right {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ambient_direct l E f).IsRightAdjoint :=
  AmbientPullbackTensor.pushRightAdjoint l E f none

private local instance ambient_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ambient_direct l E f).leftAdjoint.Additive :=
  (AmbientPullbackTensor.pullExact l E f none).1

private local instance ambient_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (ambient_direct l E f).leftAdjoint :=
  (AmbientPullbackTensor.pullExact l E f none).2.1

private local instance ambient_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (ambient_direct l E f).leftAdjoint :=
  (AmbientPullbackTensor.pullExact l E f none).2.2

private theorem derived_compositor_model
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G P
  have hc : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P =
      𝟙 _ := by
    ext n
    rfl
  rw [hc] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h, Functor.mapDerivedCategoryNatIso_fac]
  rfl

private theorem transport_section_formula {A B : Type*} (F G : A → B)
    (h : ∀ x : A, F x = G x) (x y : A) (hxy : HEq x y) : HEq (F x) (G y) := by
  exact heq_of_eq ((h x).trans (congrArg G (eq_of_heq hxy)))

private theorem compositor_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Rf : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y)
    (Rg : coefficientSequenceModules l E Y ⥤ coefficientSequenceModules l E Z)
    (Rh : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Z)
    [rf : Rf.IsRightAdjoint] [rg : Rg.IsRightAdjoint] [rh : Rh.IsRightAdjoint]
    [af : Rf.leftAdjoint.Additive] [ag : Rg.leftAdjoint.Additive]
    [ah : Rh.leftAdjoint.Additive]
    [lf : PreservesFiniteLimits Rf.leftAdjoint] [lg : PreservesFiniteLimits Rg.leftAdjoint]
    [lh : PreservesFiniteLimits Rh.leftAdjoint]
    [cf : PreservesFiniteColimits Rf.leftAdjoint]
    [cg : PreservesFiniteColimits Rg.leftAdjoint]
    [ch : PreservesFiniteColimits Rh.leftAdjoint]
    (Df : coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X)
    (Dg : coefficientSequenceDerived l E Z ⥤ coefficientSequenceDerived l E Y)
    (Dh : coefficientSequenceDerived l E Z ⥤ coefficientSequenceDerived l E X)
    (ef : DerivedCategory.Q ⋙ Df ≅
      Rf.leftAdjoint.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (eg : DerivedCategory.Q ⋙ Dg ≅
      Rg.leftAdjoint.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (eh : DerivedCategory.Q ⋙ Dh ≅
      Rh.leftAdjoint.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hef : HEq ef Rf.leftAdjoint.mapDerivedCategoryFactors)
    (heg : HEq eg Rg.leftAdjoint.mapDerivedCategoryFactors)
    (heh : HEq eh Rh.leftAdjoint.mapDerivedCategoryFactors)
    (hf : Rf = ambient_direct l E f)
    (hg : Rg = ambient_direct l E g)
    (hh : Rh = ambient_direct l E (f ≫ g))
    (d : Rf ⋙ Rg ≅ Rh)
    (hs : ∀ (N : coefficientSequenceModules l E X) (n : ℕ) (U : Z.ProEt)
        (x : ((Rf ⋙ Rg).obj N).val.obj (op (n, U)))
        (y : N.val.obj (op (n,
          (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U)))),
      HEq x y → HEq (((d.hom.app N).val.app (op (n, U))) x)
        (N.val.map (@Quiver.Hom.op (ℕ × X.ProEt) _
          (n, (proEtaleBaseChange (f ≫ g)).obj U)
          (n, (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U))
          (𝟙 n, (MorphismProperty.Over.pullbackComp f g).hom.app U)) y))
    (p : Rh.leftAdjoint ≅ Rg.leftAdjoint ⋙ Rf.leftAdjoint)
    (hp : conjugateIsoEquiv
      ((Adjunction.ofIsRightAdjoint Rg).comp (Adjunction.ofIsRightAdjoint Rf))
      (Adjunction.ofIsRightAdjoint Rh) p = d)
    (a : Dh ≅ Dg ⋙ Df)
    (ha : ∀ P : CochainComplex (coefficientSequenceModules l E Z) ℤ,
      a.hom.app (DerivedCategory.Q.obj P) ≫ Df.map (eg.hom.app P) ≫
          ef.hom.app ((Rg.leftAdjoint.mapHomologicalComplex (.up ℤ)).obj P) =
        eh.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex p (.up ℤ)).hom.app P))
    (hdf : Df = (publishedSystemAmbientData l E).pull f)
    (hdg : Dg = (publishedSystemAmbientData l E).pull g)
    (hdh : Dh = (publishedSystemAmbientData l E).pull (f ≫ g))
    (iF : Df ≅ (publishedSystemAmbientData l E).pull f)
    (iG : Dg ≅ (publishedSystemAmbientData l E).pull g)
    (iH : Dh ≅ (publishedSystemAmbientData l E).pull (f ≫ g))
    (hiF : iF = eqToIso hdf) (hiG : iG = eqToIso hdg) (hiH : iH = eqToIso hdh)
    (M : coefficientSequenceDerived l E Z) :
    a.hom.app M ≫
        iF.hom.app
          (Dg.obj M) ≫
        ((publishedSystemAmbientData l E).pull f).map
          (iG.hom.app M) =
      iH.hom.app M ≫
        ((publishedSystemAmbientData l E).comp f g).inv.app M := by
  subst Rf
  subst Rg
  subst Rh
  subst Df
  subst Dg
  subst Dh
  subst iF
  subst iG
  subst iH
  dsimp only [publishedSystemAmbientData] at ef eg eh hef heg heh a ha ⊢
  have hef' : ef = (ambient_direct l E f).leftAdjoint.mapDerivedCategoryFactors :=
    eq_of_heq hef
  have heg' : eg = (ambient_direct l E g).leftAdjoint.mapDerivedCategoryFactors :=
    eq_of_heq heg
  have heh' : eh = (ambient_direct l E (f ≫ g)).leftAdjoint.mapDerivedCategoryFactors :=
    eq_of_heq heh
  subst ef
  subst eg
  subst eh
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hd : d = (AmbientPullbackTensor.pushComp l E f g none).symm := by
    apply Iso.ext
    apply (Iso.comp_hom_eq_id (AmbientPullbackTensor.pushComp l E f g none)).1
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change ((AmbientPullbackTensor.pushComp l E f g none).hom.app N).val.app U
      ((d.hom.app N).val.app U x) = x
    erw [(AmbientPullbackTensor.pushComp_existsUnique l E f g none).exists.choose_spec]
    erw [eq_of_heq (hs N U.unop.1 U.unop.2 x x HEq.rfl)]
    change N.val.map ((AmbientPullbackTensor.baseComp f g none).inv.app U.unop).op
      (N.val.map ((AmbientPullbackTensor.baseComp f g none).hom.app U.unop).op x) = x
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.inv_hom_id_app, op_id,
      PresheafOfModules.map_id]
    rfl
  have hp' : p = (AmbientPullbackTensor.comp l E f g none).symm := by
    apply Iso.ext
    apply (conjugateEquiv
      ((AmbientPullbackTensor.adjunction l E g none).comp
        (AmbientPullbackTensor.adjunction l E f none))
      (AmbientPullbackTensor.adjunction l E (f ≫ g) none)).injective
    change (conjugateIsoEquiv _ _ p).hom = _
    have hpc : (conjugateIsoEquiv
        ((AmbientPullbackTensor.adjunction l E g none).comp
          (AmbientPullbackTensor.adjunction l E f none))
        (AmbientPullbackTensor.adjunction l E (f ≫ g) none)) p = d := hp
    exact (congrArg Iso.hom hpc).trans ((congrArg Iso.hom hd).trans
      (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).symm)
  have ha' : a = Functor.mapDerivedCategoryNatIso p ≪≫
      (Functor.mapDerivedCategoryCompIso (AmbientPullbackTensor.pull l E g none)
        (AmbientPullbackTensor.pull l E f none)).symm := by
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E Z) (.up ℤ))
    intro P
    apply (cancel_mono ((AmbientPullbackTensor.derivedPull l E f none).map
      ((AmbientPullbackTensor.pull l E g none).mapDerivedCategoryFactors.hom.app P) ≫
      (AmbientPullbackTensor.pull l E f none).mapDerivedCategoryFactors.hom.app
        (((AmbientPullbackTensor.pull l E g none).mapHomologicalComplex (.up ℤ)).obj P))).1
    simpa only [AmbientPullbackTensor.pull, AmbientPullbackTensor.derivedPull,
      ambient_direct, Category.assoc] using
      (ha P).trans (derived_compositor_model _ _ _ p P).symm
  rw [ha', hp']
  dsimp only [AmbientPullbackTensor.pull, AmbientPullbackTensor.derivedPull, ambient_direct]
  simp only [AmbientPullbackTensor.derivedComp, Functor.mapDerivedCategoryCompNatIso,
    AmbientPullbackTensor.pull, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm, Category.comp_id]
  exact Category.comp_id _

end

attribute [local implicit_reducible] pullbackTensorSequenceInverse
  pullbackTensorSequenceDerived pullbackTensorSequenceAdjunction
  pullbackTensorSequenceDirect pullbackTensorSequenceBase MorphismProperty Scheme.ProEt
  AmbientPullbackTensor.pull AmbientPullbackTensor.adjunction AmbientPullbackTensor.push
  AmbientPullbackTensor.Site AmbientPullbackTensor.base AmbientPullbackTensor.siteCategory
  AmbientPullbackTensor.topology AmbientPullbackTensor.coefficients coefficientSequenceHasDerived
  SemilinearSections.hasDerived SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint

attribute [local irreducible] publishedSystemAmbientData

/-- The section-normalized derived compositor is the inverse ambient compositor,
after the specified equality of the two inverse-image presentations.
Source: Stacks 03D3 and 07A7, and exact localization (015F)
(blueprint: lem-sf-published-system-compositor-identification).
Proof: sequence_direct_eq identifies the two ordinary direct images. The sections
field of c and pushComp_existsUnique give the same restriction along the canonical
isomorphism of fibre products, with opposite orientation. Module-sheaf morphisms
are determined on every sequence-site section, so these right-adjoint compositors
agree. Apply conjugateIsoEquiv injectivity, using c.conjugate and the definition
of AmbientPullbackTensor.comp, to identify the ordinary inverse-image compositors.
For the derived equation, restrict to the cochain localization, where c.pullComp_model
and the factor equations of mapDerivedCategoryNatIso and mapDerivedCategoryCompIso
reduce it to the ordinary equality. Cancel the invertible exact-factorization
maps. Faithfulness of restriction along localization proves the equation for all
unbounded derived objects. Only the section formula is used, so the result is
independent of the Operations package and includes arbitrary semilinear transitions. -/
theorem publishedSystemCompositorIdentification
    (o : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : coefficientSequenceDerived l E Z) :
    let a : pullbackTensorSequenceDerived l E (f ≫ g) ≅
        pullbackTensorSequenceDerived l E g ⋙ pullbackTensorSequenceDerived l E f :=
      c.pullComp f g
    a.hom.app M ≫
        (WeilConjectures.publishedSystemAmbientPullIso l E f).hom.app
          ((pullbackTensorSequenceDerived l E g).obj M) ≫
        ((publishedSystemAmbientData l E).pull f).map
          ((WeilConjectures.publishedSystemAmbientPullIso l E g).hom.app M) =
      (WeilConjectures.publishedSystemAmbientPullIso l E (f ≫ g)).hom.app M ≫
        ((publishedSystemAmbientData l E).comp f g).inv.app M := by
  exact compositor_normalization l E f g
    (pullbackTensorSequenceDirect l E f) (pullbackTensorSequenceDirect l E g)
    (pullbackTensorSequenceDirect l E (f ≫ g))
    (rf := pullbackTensorSequenceDirect_rightAdjoint l E f)
    (rg := pullbackTensorSequenceDirect_rightAdjoint l E g)
    (rh := pullbackTensorSequenceDirect_rightAdjoint l E (f ≫ g))
    (af := pullbackTensorSequenceInverse_additive l E f)
    (ag := pullbackTensorSequenceInverse_additive l E g)
    (ah := pullbackTensorSequenceInverse_additive l E (f ≫ g))
    (lf := pullbackTensorSequenceInverse_limits l E f)
    (lg := pullbackTensorSequenceInverse_limits l E g)
    (lh := pullbackTensorSequenceInverse_limits l E (f ≫ g))
    (cf := pullbackTensorSequenceInverse_colimits l E f)
    (cg := pullbackTensorSequenceInverse_colimits l E g)
    (ch := pullbackTensorSequenceInverse_colimits l E (f ≫ g))
    (pullbackTensorSequenceDerived l E f) (pullbackTensorSequenceDerived l E g)
    (pullbackTensorSequenceDerived l E (f ≫ g))
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors
    (pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors
    (pullbackTensorSequenceInverse l E (f ≫ g)).mapDerivedCategoryFactors
    HEq.rfl HEq.rfl HEq.rfl
    (sequence_direct_eq l E f) (sequence_direct_eq l E g)
    (sequence_direct_eq l E (f ≫ g)) (c.ordinaryDirect f g)
    (fun N n U ↦ transport_section_formula _ _ (c.sections f g N n U))
    (c.ordinaryPull f g) (c.conjugate f g)
    (c.pullComp f g) (c.pullComp_model f g)
    (publishedSystemAmbientPull_eq l E f)
    (publishedSystemAmbientPull_eq l E g) (publishedSystemAmbientPull_eq l E (f ≫ g))
    (publishedSystemAmbientPullIso l E f) (publishedSystemAmbientPullIso l E g)
    (publishedSystemAmbientPullIso l E (f ≫ g))
    (by unfold publishedSystemAmbientPullIso; rfl)
    (by unfold publishedSystemAmbientPullIso; rfl)
    (by unfold publishedSystemAmbientPullIso; rfl) M

end WeilConjectures
