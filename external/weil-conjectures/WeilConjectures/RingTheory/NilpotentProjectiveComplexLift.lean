/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import all WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import all WeilConjectures.Algebra.Homology.NilpotentDerivedUpperBound
import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.NilpotentProjectiveModuleLift

/-!
# Lifting a prescribed projective complex through a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 09AR, lemma-lift-complex-projectives
(auxiliary; not a blueprint node).

The proof uses the ordinary-module filtration argument already proved in
`NilpotentDerivedUpperBound`. Its public theorem is formulated on a one-object site;
`import all` also makes its proved ordinary-module helper available here.
The tensor API has equal ring and module universes. Restriction along the ring equivalence
`ULift A ≃+* A` transports that API to the larger module universe of this statement.
Uniqueness of universal derived functors handles the independently chosen derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w' w₀ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Pointwise ChangeOfRings

namespace CochainComplex

-- Transport universal derived functors through exact equivalences. The generic Kan
-- extension helpers come from DerivedExtensionRingEquivRawTransportIso; unlike its public
-- ring-specific theorem, these helpers impose no equality between the ring universes.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_extension_transport
    {C₀ D₀ C D : Type*} [Category* C₀] [Category* D₀] [Category* C] [Category* D]
    [Abelian C₀] [Abelian D₀] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₀} C₀] [HasDerivedCategory.{w₁} D₀]
    [HasDerivedCategory.{w₂} C] [HasDerivedCategory.{w₃} D]
    (F₀ : C₀ ⥤ D₀) [F₀.Additive] (F : C ⥤ D) [F.Additive]
    (eC : C ≌ C₀) [eC.functor.Additive] (eD : D ≌ D₀) [eD.functor.Additive]
    (t : eC.functor ⋙ F₀ ≅ F ⋙ eD.functor)
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory D₀)
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶ F₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ))]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))] :
    Nonempty (eC.functor.mapDerivedCategory ⋙ L₀ ≅ L ⋙ eD.functor.mapDerivedCategory) := by
  let SC := eC.functor.mapHomologicalComplex (.up ℤ)
  let T₀ := F₀.mapHomologicalComplex (.up ℤ)
  let T := F.mapHomologicalComplex (.up ℤ)
  let SD := eD.functor.mapHomologicalComplex (.up ℤ)
  let E := eD.functor.mapDerivedCategory
  have : SC.IsEquivalence := (eC.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  have : eC.functor.mapDerivedCategory.IsEquivalence := ModuleCat.derived_equivalence eC
  have : E.IsEquivalence := ModuleCat.derived_equivalence eD
  obtain ⟨α₀, hα₀⟩ := ModuleCat.complex_universal F₀ L₀ ε₀ inferInstance
  let := hα₀
  let αpre := (Functor.associator SC DerivedCategory.Q L₀).hom ≫
    Functor.whiskerLeft SC α₀
  have hpre := (Functor.isRightKanExtension_iff_precomp L₀ SC α₀).mp hα₀
  let β₀ := (Functor.associator DerivedCategory.Q eC.functor.mapDerivedCategory L₀).inv ≫
    Functor.whiskerRight eC.functor.mapDerivedCategoryFactors.hom L₀ ≫ αpre
  let hβ₀ := (Functor.isRightKanExtension_iff_postcomp₁ eC.functor.mapDerivedCategory
    eC.functor.mapDerivedCategoryFactors αpre).mp hpre
  let := hβ₀
  obtain ⟨α, hα⟩ := ModuleCat.complex_universal F L ε inferInstance
  let := hα
  let αpost := (Functor.associator DerivedCategory.Q L E).inv ≫ Functor.whiskerRight α E
  let := ModuleCat.kan_postcomp_equivalence DerivedCategory.Q _ L E α
  obtain ⟨β, hβ⟩ := ModuleCat.kan_change_iso (L ⋙ E) (Iso.refl DerivedCategory.Q)
    (Functor.associator T DerivedCategory.Q E) αpost
  let := hβ
  let tc : SC ⋙ T₀ ≅ T ⋙ SD :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex t (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  let ordinary : SC ⋙ T₀ ⋙ DerivedCategory.Q ≅ T ⋙ DerivedCategory.Q ⋙ E :=
    (Functor.associator SC T₀ DerivedCategory.Q).symm ≪≫
      Functor.isoWhiskerRight tc DerivedCategory.Q ≪≫
      Functor.associator T SD DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft T eD.functor.mapDerivedCategoryFactors.symm
  exact ⟨Functor.rightKanExtensionUniqueOfIso
    (eC.functor.mapDerivedCategory ⋙ L₀) β₀ ordinary (L ⋙ E) β⟩

-- Adjoint uniqueness gives the change-of-rings square also for different ring universes.
private noncomputable def extend_equiv_iso_restrict
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ModuleCat.extendScalars e.symm.toRingHom ≅ ModuleCat.restrictScalars.{max u v} e :=
  Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj e.symm.toRingHom)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction

private noncomputable def extend_comp_iso
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    ModuleCat.extendScalars.{u, w, max u v w} (g.comp f) ≅
      ModuleCat.extendScalars.{u, v, max u v w} f ⋙
        ModuleCat.extendScalars.{v, w, max u v w} g :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, v, w} g))
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, w} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp.{max u v w} f g).symm

private noncomputable def extension_square
    {R₀ B₀ : Type u} {R B : Type v}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    (f₀ : R₀ →+* B₀) (f : R →+* B) (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hf : eB.toRingHom.comp f₀ = f.comp eR.toRingHom) :
    ModuleCat.restrictScalars.{max u v} eR.toRingHom ⋙ ModuleCat.extendScalars f₀ ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars.{max u v} eB.toRingHom := by
  have h : f₀.comp eR.symm.toRingHom = eB.symm.toRingHom.comp f := by
    ext r
    apply eB.injective
    simpa using RingHom.congr_fun hf (eR.symm r)
  exact Functor.isoWhiskerRight (extend_equiv_iso_restrict eR).symm _ ≪≫
    (extend_comp_iso eR.symm.toRingHom f₀).symm ≪≫
    eqToIso (congrArg (fun g ↦ ModuleCat.extendScalars.{v, u, max u v} g) h) ≪≫
    extend_comp_iso f eB.symm.toRingHom ≪≫
    Functor.isoWhiskerLeft _ (extend_equiv_iso_restrict eB)

-- Work first where ring and module universes agree, using the existing K-flat API.
private theorem native_preserves_kFlat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars f).PreservesKFlatQuasiIso :=
  ⟨fun hK hL a ↦ scalarExtension_quasiIso_of_kFlat f a
    (show QuasiIso a from inferInstance) hK hL⟩

private theorem acyclic_tensor_of_kFlat
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.Acyclic) :
    (mapBifunctor F P (MonoidalCategory.curriedTensor _)).Acyclic := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).2 hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (mapBifunctor F P (MonoidalCategory.curriedTensor _))).1
      (hP ((HomotopyCategory.quotient _ _).obj F) hF').2

private theorem native_counit_isIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) := by
  have (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  have : (ModuleCat.extendScalars f).PreservesKFlatQuasiIso :=
    ⟨fun hK hL a ↦ scalarExtension_quasiIso_of_kFlat f a
      (show QuasiIso a from inferInstance) hK hL⟩
  exact ((ModuleCat.extendScalars f).isLeftDerivedFunctor_iff_isIso_app_of_kFlat ε).1
    inferInstance P hP

private theorem native_upper_bound
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (C : DerivedCategory (ModuleCat.{u} A)) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I)) i).obj (L.obj C))) :
    ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj C) := by
  let G := DerivedCategory.Q.objPreimage C
  obtain ⟨P, f, hf, hflat, hk⟩ := exists_quasiIso_flat_kFlat G
  let : QuasiIso f := hf
  let e : DerivedCategory.Q.obj P ≅ C :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso C
  have := native_counit_isIso (Ideal.Quotient.mk I) L ε P hk
  let eModel : L.obj C ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex (.up ℤ)).obj P) :=
    (L.mapIso e).symm ≪≫
      (L.mapIso ((DerivedCategory.quotientCompQhIso _).app P)).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      DerivedCategory.Qh.mapIso
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategoryFactors
          (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  have hbP (i : ℤ) (hi : b < i) : IsZero
      ((((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P).homology i) :=
    ((hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eModel).symm).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app _).symm
  have hP := DerivedCategory.ordinary_nilpotent_upper_bound I N hI P
    (fun i ↦ (ModuleCat.flat_iff_flat _).1 (hflat i))
    (acyclic_tensor_of_kFlat P hk) b hbP
  intro i hi
  exact ((hP i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app P)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm

-- Lift the coefficient ring, not the module, to apply the equal-universe tensor API.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nilpotent_upper_bound
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (A ⧸ I)) i).obj (L.obj C))) :
    ∀ i : ℤ, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj C) := by
  let A' := ULift.{v} A
  let eA : A ≃+* A' := ULift.ringEquiv.symm
  let J := I.map eA.toRingHom
  let eB : (A' ⧸ J) ≃+* (A ⧸ I) := (Ideal.quotientEquiv I J eA rfl).symm
  let eC := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v} eA.symm
  let eD := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v} eB
  let := HasDerivedCategory.standard (ModuleCat.{max u v} A')
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (A' ⧸ J))
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let F' := ModuleCat.extendScalars (Ideal.Quotient.mk J)
  have : F'.PreservesKFlatQuasiIso := native_preserves_kFlat _
  have (M : ModuleCat.{max u v} A') : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{max u v} A')).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{max u v} A') :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{max u v} A')
      (AsSmall.equiv (C := ℤ)).symm
  let L' := F'.leftDerivedFunctor
  let ε' := F'.leftDerivedFunctorCounit
  have hsq : eB.toRingHom.comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mk I).comp eA.symm.toRingHom := by
    ext a
    exact Ideal.quotientEquiv_symm_mk I J eA rfl a
  obtain ⟨et⟩ := derived_extension_transport F' F eC eD
    (extension_square (Ideal.Quotient.mk J) (Ideal.Quotient.mk I) eA.symm eB hsq)
    L' ε' L ε
  have hJ : J ^ N = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have hred (i : ℤ) (hi : b < i) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (A' ⧸ J)) i).obj
        (L'.obj (eC.functor.mapDerivedCategory.obj C))) := by
    have hz := eD.functor.isZero_homologyFunctor_mapDerivedCategory_obj (hb i hi)
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (et.app C))
  have hC := native_upper_bound J N hJ L' ε'
    (eC.functor.mapDerivedCategory.obj C) b hred
  intro i hi
  exact eC.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (hC i hi)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projective_reduction_comparison
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} B)]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i : ℤ, Module.Projective A (K.X i)) :
    Nonempty (L.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let A' := ULift.{v} A
  let B' := ULift.{v} B
  let eA : A' ≃+* A := ULift.ringEquiv
  let eB : B' ≃+* B := ULift.ringEquiv
  let f' := eB.symm.toRingHom.comp (f.comp eA.toRingHom)
  let eC := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v} eA
  let eD := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v} eB
  let := HasDerivedCategory.standard (ModuleCat.{max u v} A')
  let := HasDerivedCategory.standard (ModuleCat.{max u v} B')
  let F := ModuleCat.extendScalars f
  let F' := ModuleCat.extendScalars f'
  have : F'.PreservesKFlatQuasiIso := native_preserves_kFlat _
  have (M : ModuleCat.{max u v} A') : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{max u v} A')).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{max u v} A') :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{max u v} A')
      (AsSmall.equiv (C := ℤ)).symm
  let L' := F'.leftDerivedFunctor
  let ε' := F'.leftDerivedFunctorCounit
  have hsq : eB.toRingHom.comp f' = f.comp eA.toRingHom := by
    ext a
    exact eB.apply_symm_apply _
  let t := extension_square f' f eA eB hsq
  obtain ⟨et⟩ := derived_extension_transport F' F eC eD t L' ε' L ε
  let K' : CochainComplex (ModuleCat.{max u v} A') ℤ :=
    (eC.functor.mapHomologicalComplex (.up ℤ)).obj K
  have : K'.IsStrictlyLE b := inferInstance
  have hflat (i : ℤ) : ObjectProperty.flat (K'.X i) := by
    have : Module.Projective A (K.X i) := hK i
    have hp : Projective (K'.X i) :=
      (eC.map_projective_iff (K.X i)).2 inferInstance
    have : Module.Projective A' (K'.X i) := inferInstance
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hk := kFlat_of_isStrictlyLE_of_flat K' b hflat
  have := native_counit_isIso f' L' ε' K' hk
  let enative : L'.obj (DerivedCategory.Q.obj K') ≅ DerivedCategory.Q.obj
      ((F'.mapHomologicalComplex (.up ℤ)).obj K') :=
    (L'.mapIso ((DerivedCategory.quotientCompQhIso _).app K')).symm ≪≫
      asIso (ε'.app ((HomotopyCategory.quotient _ _).obj K')) ≪≫
      DerivedCategory.Qh.mapIso ((F'.mapHomotopyCategoryFactors (.up ℤ)).app K') ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} B')).app
        ((F'.mapHomologicalComplex (.up ℤ)).obj K')
  let tc : eC.functor.mapHomologicalComplex (.up ℤ) ⋙ F'.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ eD.functor.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex t (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  have : eD.functor.mapDerivedCategory.IsEquivalence := ModuleCat.derived_equivalence eD
  exact ⟨eD.functor.mapDerivedCategory.preimageIso
    ((et.app (DerivedCategory.Q.obj K)).symm ≪≫
      L'.mapIso (eC.functor.mapDerivedCategoryFactors.app K) ≪≫ enative ≪≫
      DerivedCategory.Q.mapIso (tc.app K) ≪≫
      (eD.functor.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj K)).symm)⟩

-- Extension along the quotient map is the ordinary quotient by I, as an A/I-module.
private noncomputable def reductionIso
    {A : Type u} [CommRing A] (I : Ideal A) (P : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≅
      ModuleCat.of (A ⧸ I) (P ⧸ I • (⊤ : Submodule A P)) := by
  let e := TensorProduct.quotTensorEquivQuotSMul P I
  let e' : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≃ₗ[A ⧸ I]
      (P ⧸ I • (⊤ : Submodule A P)) :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul a x }
  exact e'.toModuleIso

private theorem projective_class_closed
    {A : Type u} [CommRing A] (P₁ P₂ P₁₂ : ModuleCat.{max u v} A)
    (he : Nonempty (P₁₂ ≅ ModuleCat.of A (P₁ × P₂))) :
    (Module.Projective A P₁ ∧ Module.Projective A P₁₂ ↔
      Module.Projective A P₁ ∧ Module.Projective A P₂) := by
  obtain ⟨e⟩ := he
  constructor
  · rintro ⟨h₁, h₁₂⟩
    have := Module.Projective.of_equiv' e.toLinearEquiv
    exact ⟨h₁, Module.Projective.of_split
      (LinearMap.inr A P₁ P₂) (LinearMap.snd A P₁ P₂) (by ext; rfl)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, Module.Projective.of_equiv' e.symm.toLinearEquiv⟩

private theorem surjective_of_nilpotent_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hI : I ^ N = ⊥)
    {P₁ P₂ : ModuleCat.{max u v} A} (f : P₁ ⟶ P₂)
    (hf : Function.Surjective
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)) :
    Function.Surjective f := by
  let S := LinearMap.range f.hom
  let T := P₂ ⧸ S
  let q : P₂ →ₗ[A] T := S.mkQ
  have hquot : Function.Surjective
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (ModuleCat.ofHom q)) := by
    rw [← ModuleCat.epi_iff_surjective]
    have : Epi (ModuleCat.ofHom q) := (ModuleCat.epi_iff_surjective _).2 S.mkQ_surjective
    exact (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map_epi _
  have hzero : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map
      (ModuleCat.ofHom q : P₂ ⟶ ModuleCat.of A T) = 0 := by
    have hcomp : f ≫ ModuleCat.ofHom q = 0 := by
      ext x
      exact (Submodule.Quotient.mk_eq_zero S).2 (LinearMap.mem_range_self f.hom x)
    have hepi : Epi ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) :=
      (ModuleCat.epi_iff_surjective _).2 hf
    apply (cancel_epi ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)).mp
    rw [← Functor.map_comp, hcomp, Functor.map_zero, comp_zero]
  have hTred : Subsingleton
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of A T)) := by
    rw [hzero] at hquot
    exact ⟨fun x y ↦ by
      obtain ⟨a, ha⟩ := hquot x
      obtain ⟨b, hb⟩ := hquot y
      exact ha.symm.trans hb⟩
  have : Subsingleton (T ⧸ I • (⊤ : Submodule A T)) :=
    (reductionIso I (ModuleCat.of A T)).toLinearEquiv.symm.injective.subsingleton
  have hT : I • (⊤ : Submodule A T) = ⊤ := by
    apply top_unique
    intro x _
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact Subsingleton.elim _ _
  have hp (n : ℕ) : I ^ n • (⊤ : Submodule A T) = ⊤ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Submodule.mul_smul, hT, ih]
  have ht0 : (⊤ : Submodule A T) = ⊥ := by
    rw [← hp N, hI, Submodule.bot_smul]
  intro y
  have hy : q y = 0 := by
    have h := ht0.le (Submodule.mem_top (x := q y))
    exact h
  exact (Submodule.Quotient.mk_eq_zero S).mp hy

/-- A bounded-above projective model of derived reduction lifts as a complex, not merely
as a derived object. Source: Stacks Project, More on Algebra, Tag 09AR
(auxiliary; not a blueprint node).

The functor `L`, with its universal counit `ε`, is the total left derived functor of
termwise extension of scalars, as in `lem-pur-derived-change-of-rings` on the one-object
site. Thus `L.obj C` is `C ⊗ᴸ A/I`; no boundedness of `C` is assumed.
Extension of scalars along the quotient map is canonically the termwise quotient by `I`.

Proof:
1. Take the class of all projective A-modules. The lifting property of
   `def-weil-pbc-projective-module` gives closure under sums and summands. If T/IT = 0,
   then T = IT = ... = I^N T = 0. Apply this to a cokernel to see that a map which is
   surjective modulo I is surjective. These verify conditions (1), (2), (3) of Tag 0BCA.
2. By `lem-weil-pbc-nilpotent-projective-module-lift`, lift every E^i to a projective
   A-module. Together with the upper bound on E, this verifies condition (4).
3. Choose an upper bound b on E. Its cohomology vanishes above b, hence so does that
   of the derived reduction of C. By `lem-weil-pbc-nilpotent-derived-upper-bound`, the
   cohomology of C vanishes above b as well.
4. Apply `lem-weil-pbc-bounded-above-projective-model` to obtain a bounded-above
   projective representative of C, verifying condition (5), without assuming
   pseudo-coherence or finite Tor amplitude.
5. Apply `lem-sc-complex-lift-class-projective`. It supplies P representing C and a
   complex isomorphism between its termwise reduction and the prescribed E. -/
theorem exists_projective_lift_of_nilpotent
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (E : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i))
    (hReduction : Nonempty (L.obj C ≅ DerivedCategory.Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) := by
  obtain ⟨N, hN, hnil⟩ := hI
  let Pclass : Set (ModuleCat.{max u v} A) := {P | Module.Projective A P}
  apply AlgebraicGeometry.complex_lift_class_projective A I Pclass C E
  · intro P hP
    let : Module.Projective A P := hP
    infer_instance
  · exact projective_class_closed
  · intro P₁ P₂ f _ _ hf
    exact surjective_of_nilpotent_reduction I N hnil f hf
  · exact hEbound
  · intro i
    let : Module.Projective (A ⧸ I) (E.X i) := hEproj i
    obtain ⟨P, hP, ⟨e⟩⟩ :=
      Module.exists_projective_lift_of_nilpotent_ideal A I N hN hnil (E.X i)
    exact ⟨P, hP, ⟨e.symm.toModuleIso ≪≫ (reductionIso I P).symm⟩⟩
  · obtain ⟨b, hb⟩ := hEbound
    have hC : ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj C) := by
      apply nilpotent_upper_bound I N hnil L ε C b
      let : E.IsStrictlyLE b := hb
      obtain ⟨ered⟩ := hReduction
      intro i hi
      have hz := (DerivedCategory.isLE_iff (DerivedCategory.Q.obj E) b).1
        inferInstance i hi
      exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso ered)
    obtain ⟨K, hKproj, hKb, ⟨eK⟩⟩ :=
      DerivedCategory.exists_boundedAbove_projective_model A C b hC
    have hKb' : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).2 hKb
    have heK : Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (.up ℤ)).obj K) ≅ L.obj (DerivedCategory.Q.obj K)) := by
      let : K.IsStrictlyLE b := hKb'
      obtain ⟨e⟩ := projective_reduction_comparison (Ideal.Quotient.mk I) L ε K b hKproj
      exact ⟨e.symm⟩
    obtain ⟨ered⟩ := hReduction
    obtain ⟨eComp⟩ := heK
    exact ⟨K, ⟨b, hKb'⟩, hKproj, ⟨eK⟩, ⟨eComp ≪≫ L.mapIso eK ≪≫ ered⟩⟩

end CochainComplex
