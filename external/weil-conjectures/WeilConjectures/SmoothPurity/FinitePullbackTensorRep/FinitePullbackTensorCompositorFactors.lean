/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact pullback composition in finite representative coordinates

Source: Stacks Project, Tags 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-compositor-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem derive_conjugate_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F F' : A ⥤ B) (G G' : B ⥤ C) (K K' : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [K.Additive] [K'.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    [Limits.PreservesFiniteLimits K] [Limits.PreservesFiniteColimits K]
    [Limits.PreservesFiniteLimits K'] [Limits.PreservesFiniteColimits K']
    (rF : F ≅ F') (rG : G ≅ G') (rK : K ≅ K') (c : K' ≅ F' ⋙ G') :
    (Functor.mapDerivedCategoryNatIso
      (rK ≪≫ c ≪≫ Functor.isoWhiskerRight rF.symm G' ≪≫
        Functor.isoWhiskerLeft F rG.symm)).hom ≫
        (Functor.mapDerivedCategoryCompIso F G).inv =
      (Functor.mapDerivedCategoryNatIso rK).hom ≫
        (Functor.mapDerivedCategoryNatIso c).hom ≫
        (Functor.mapDerivedCategoryCompIso F' G').inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso rF).inv G'.mapDerivedCategory ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso rG).inv := by
  simp only [Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight rF.symm G')]
  simp only [Functor.mapDerivedCategoryNatIso_symm]

private theorem exact_compositor_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (K : A ⥤ C)
    [F.Additive] [G.Additive] [K.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits K] [Limits.PreservesFiniteColimits K]
    (a : K ≅ F ⋙ G) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      K.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso a.symm (.up ℤ)).inv.app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  exact Functor.mapDerivedCategoryNatIso_fac a P

private theorem transport_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F F' : A ⥤ B) (G G' : B ⥤ C) (K K' : A ⥤ C)
    (rF : F ≅ F') (rG : G ≅ G') (rK : K ≅ K')
    (c : K' ⟶ F' ⋙ G') (d : K ⟶ F ⋙ G)
    (hd : d = rK.hom ≫ c ≫ Functor.whiskerRight rF.inv G' ≫
      Functor.whiskerLeft F rG.inv)
    (M : A) (N : B) (S T : C)
    (eF : F.obj M ⟶ N) (eG : G.obj N ⟶ T) (eK : K.obj M ⟶ S)
    (a : S ⟶ T)
    (h : d.app M ≫ G.map eF ≫ eG = eK ≫ a) :
    c.app M ≫ G'.map (rF.inv.app M ≫ eF) ≫ (rG.inv.app N ≫ eG) =
      (rK.inv.app M ≫ eK) ≫ a := by
  have hn := rG.inv.naturality eF
  change G'.map eF ≫ rG.inv.app N =
    rG.inv.app (F.obj M) ≫ G.map eF at hn
  have hm := congr_app hd M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hm
  apply (cancel_epi (rK.hom.app M)).1
  simp only [G'.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  calc
    _ = d.app M ≫ G.map eF ≫ eG := by rw [hm]; simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Iso.hom_inv_id_app_assoc]

namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
open CategoryTheory.Functor

attribute [local semireducible] pull

attribute [local instance] modules_abelian modules_derived ordinary_additive
  ordinary_limits ordinary_colimits
attribute [local implicit_reducible] modules_abelian modules_derived

/-- The intrinsic derived compositor agrees with the conjugated ordinary computation maps.
Source: Stacks 00YV and exact termwise localization in 0735
(blueprint: lem-pur-finite-pullback-tensor-compositor-factors).
Proof: the localization of a conjugated module compositor is the corresponding
conjugation of its localization, by compatibility with natural isomorphisms and
composition. For ordinary exact functors, the compositor and computation maps
satisfy mapDerivedCategoryCompIso_hom_app_factors. Naturality of the three
realization comparisons moves them across these maps; the inverse pairs cancel.
This gives the computation equation on every complex, independently of flatness. -/
theorem compositor_fac {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        (DerivedCategory.Q.obj P) ≫
        (finiteDerivedPullback l E n h).map ((factors l E f n).hom.app P) ≫
        (factors l E h n).hom.app ((pull l E f n).obj P) =
      (factors l E (h ≫ f) n).hom.app P ≫
        DerivedCategory.Q.map ((complexComp l E f h n).hom.app P) := by
  let := ordinary_additive l E f n
  let := ordinary_additive l E h n
  let := ordinary_additive l E (h ≫ f) n
  let := ordinary_limits l E f n
  let := ordinary_limits l E h n
  let := ordinary_limits l E (h ≫ f) n
  let := ordinary_colimits l E f n
  let := ordinary_colimits l E h n
  let := ordinary_colimits l E (h ≫ f) n
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) h
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) (h ≫ f)
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) h
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) (h ≫ f)
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) h
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) (h ≫ f)
  let OF := ordinary l E f n
  let OH := ordinary l E h n
  let OK := ordinary l E (h ≫ f) n
  let IF := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let IH := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) h
  let IK := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) (h ≫ f)
  let rF := realization l E f n
  let rH := realization l E h n
  let rK := realization l E (h ≫ f) n
  have hd := derive_conjugate_comp OF IF OH IH OK IK
    (pullbackTensorFiniteRealization l E f n)
    (pullbackTensorFiniteRealization l E h n)
    (pullbackTensorFiniteRealization l E (h ≫ f) n)
    (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h f)
  have ht := transport_fac OF.mapDerivedCategory IF.mapDerivedCategory
    OH.mapDerivedCategory IH.mapDerivedCategory OK.mapDerivedCategory IK.mapDerivedCategory
    rF rH rK
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom
    (mapDerivedCategoryNatIso (moduleComp l E f h n) ≪≫
      (mapDerivedCategoryCompIso OF OH).symm).hom
    (by
      dsimp only [rF, rH, rK, OF, OH, OK, IF, IH, IK, moduleComp, realization] at hd ⊢
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        sfIntrinsicDerivedPullbackComp] using hd)
    (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj ((pull l E f n).obj P))
    (DerivedCategory.Q.obj ((pull l E (h ≫ f) n).obj P))
    (DerivedCategory.Q.obj ((pull l E h n).obj ((pull l E f n).obj P)))
    (OF.mapDerivedCategoryFactors.hom.app P)
    (OH.mapDerivedCategoryFactors.hom.app ((pull l E f n).obj P))
    (OK.mapDerivedCategoryFactors.hom.app P)
    (DerivedCategory.Q.map ((complexComp l E f h n).hom.app P))
    (by
      unfold complexComp pull
      simpa only [id_eq, Iso.symm_hom, OF, OH, OK, Functor.comp_obj] using
        exact_compositor_fac OF OH OK (moduleComp l E f h n) P)
  unfold factors
  dsimp only [id]
  dsimp only [rF, rH, rK, OF, OH, OK, IF, IH, IK] at ht
  simp only [realization, ordinary, finiteDerivedPullback,
    sfIntrinsicDerivedPullback, ordinaryFactors, proEtaleRingDerivedPullbackFactors,
    Iso.trans_hom, Functor.comp_obj,
    Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app] at ht ⊢
  convert ht using 1 <;> rfl

end WeilConjectures.FinitePullbackTensorRep
