/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExact
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # Comparing discrete quotient coefficients after internal realization

Source: integral-models proof (1), Stacks Tags 00YV and 099I.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private local instance forgetAbFiltered : PreservesFilteredColimits
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  comp_preservesFilteredColimits (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})

private local instance pointPreserves :
    (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _

private def pointIso (A : Type u) [CommRing A] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ discreteObj A :=
  ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).symm

private theorem pointIso_fac (A : Type u) [CommRing A] :
    toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
        (pointIso A).hom.hom =
      Functor.whiskerRight
        (toSheafify (coherentTopology Profinite.{u})
          ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  change _ ≫ (sheafifyMap (coherentTopology Profinite.{u})
      (Functor.constComp Profinite.{u}ᵒᵖ (CommRingCat.of (ULift.{u + 1} A))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
    (sheafifyComposeIso _ _ _).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafComposeIso_hom_fac]
  ext U a
  rfl

private theorem pointIso_mon (A : Type u) [CommRing A] :
    IsMonHom (pointIso A).hom := by
  let J := coherentTopology Profinite.{u}
  let B := ULift.{u + 1} A
  let g : (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of B) ⟶
      (discreteSheaf A).obj :=
    Functor.whiskerRight
      (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of B)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let ψ := (presheafToSheaf J Ab.{u + 1}).map
    (Functor.whiskerRight g (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
      (Sheaf.sheafifyRingPresheafIso J (discreteSheaf A)).hom
  have hψ : IsMonHom ψ := by dsimp only [ψ]; infer_instance
  have hm := constantSheafRingMonObj J B
  have hψ' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B)) _ ψ :=
    IsMonHom.of_eq ψ hm.symm rfl (hf := hψ)
  have heq : (pointIso A).hom = ψ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (discreteObj A).property
    rw [pointIso_fac]
    exact ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
      (discreteObj A)).apply_symm_apply (Functor.whiskerRight g
        (forget₂ RingCat.{u + 1} Ab.{u + 1})) |>.symm
  rw [heq]
  exact hψ'

private def schemeIso (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ condensedRingObj (discreteObj A) X :=
  (constantSchemeIso X).app _ ≪≫ (upperStarFromPoint X).mapIso (pointIso A)

private theorem schemeIso_mon (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsMonHom (schemeIso X A).hom := by
  let := pointIso_mon A
  have h := Functor.isMonHom_compAlgHom
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (upperStarFromPoint X) (constantSchemeIso X).inv
    (AddCommGrpCat.of (ULift.{u + 1} A))
  have hh := monHomInvExplicit _ _
    ((constantSchemeIso X).app (AddCommGrpCat.of (ULift.{u + 1} A))).symm h
  have hmap : IsMonHom ((upperStarFromPoint X).map (pointIso A).hom) := inferInstance
  dsimp only [schemeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact monHomCompExplicit _ _ _ _ _ hh hmap

private def ringIso (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} A)) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X)
        (condensedRingObj (discreteObj A) X) := by
  let := schemeIso_mon X A
  let φ := AdmissibleScalarRealization.constantRingMap A X _ (schemeIso X A).hom
  letI : IsIso φ := AdmissibleScalarRealization.constantRingMap_isIso A X _
    (schemeIso X A).hom
  exact asIso φ

private def liftHom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{u + 1} A →+* ULift.{u + 1} B :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

private theorem pointIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (liftHom f).toAddMonoidHom) ≫ (pointIso B).hom =
      (pointIso A).hom ≫ discreteMap f := by
  exact ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).inv.naturality
        (CommRingCat.ofHom (liftHom f)))

private theorem schemeIso_naturality (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (liftHom f).toAddMonoidHom) ≫ (schemeIso X B).hom =
      (schemeIso X A).hom ≫ (upperStarFromPoint X).map (discreteMap f) := by
  dsimp only [schemeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, (constantSchemeIso X).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, pointIso_naturality, Functor.map_comp]
  simp only [Category.assoc]

private theorem ringIso_naturality (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (liftHom f)) ≫ (ringIso X B).hom =
      (ringIso X A).hom ≫ sectionMap X ((upperStarFromPoint X).map (discreteMap f)) := by
  let := schemeIso_mon X A
  let := schemeIso_mon X B
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj (discreteObj B) X)).property
  ext U a
  have hn := toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map
      (CommRingCat.ofHom (liftHom f)))
  have hn' := ConcreteCategory.congr_hom (congr_app hn U) a
  dsimp only [NatTrans.comp_app, Functor.const_map_app, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at hn'
  change (ringIso X B).hom.hom.app U
    ((sheafifyMap (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (liftHom f)))).app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  rw [← hn']
  change (AdmissibleScalarRealization.constantRingMap B X _ (schemeIso X B).hom).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U
          ((liftHom f) a)) = _
  rw [AdmissibleScalarRealization.constantRingMap_normalization]
  change _ = ((upperStarFromPoint X).map (discreteMap f)).hom.app U
    ((AdmissibleScalarRealization.constantRingMap A X _ (schemeIso X A).hom).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a))
  rw [AdmissibleScalarRealization.constantRingMap_normalization]
  have h := ConcreteCategory.congr_hom (congr_app
    (congrArg (fun g ↦ g.hom) (schemeIso_naturality X f)) U)
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
  have hnAb := ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map
        (AddCommGrpCat.ofHom (liftHom f).toAddMonoidHom))) U) a
  change (schemeIso X B).hom.hom.app U
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app U
        ((liftHom f) a)) = _
  dsimp only [NatTrans.comp_app, Functor.const_map_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, AddCommGrpCat.hom_ofHom] at hnAb
  exact (congrArg (fun b ↦ (schemeIso X B).hom.hom.app U b) hnAb).trans h

private def smallConstantIso (X : Scheme.{u}) :
    constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1} ≅
      constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
        (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
          X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
            (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) :=
by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  have : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsEquivalence := e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.ProEt.topology X) := by
    change Functor.IsDenseSubsite
      (Functor.inducedTopology
        (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt)
        (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X) AsSmall.down
    infer_instance
  exact (e.constantSheafSheafCongrIso (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    CommRingCat.{u + 1} (proEtIsTerminal (proEtTerminal X))).symm

private def smallIso (X : Scheme.{u}) (A : Type u) [CommRing A] :
    ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (ULift.{u + 1} A) ≅ smallRing X (condensedRingObj (discreteObj A) X) :=
  (smallConstantIso X).app (CommRingCat.of (ULift.{u + 1} A)) ≪≫
    ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).mapIso
      (ringIso X A)

private theorem smallIso_naturality (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (liftHom f)) ≫ (smallIso X B).hom =
      (smallIso X A).hom ≫ smallMap X ((upperStarFromPoint X).map (discreteMap f)) := by
  dsimp only [smallIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, smallMap]
  rw [← Category.assoc, (smallConstantIso X).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, ringIso_naturality, Functor.map_comp]
  simp only [Category.assoc]

/-- Discrete quotient coefficients commute with the actual internal realization.

Source: integral-models proof (1); Stacks Tags 00YV and 099I.
(auxiliary; not a blueprint node).

Proof: the monoidal constant-sheaf/inverse-image comparison identifies the pullback
of the underlying abelian ring of the discrete constant sheaf of A with the
constant abelian ring on the scheme. Reconstructing section rings carries this
monoidal comparison to a ring-sheaf isomorphism. Precomposition along AsSmall.down
commutes with constant sheaves, since it is a site equivalence. Apply this to A
and A/I. The ring equivalence ULift A = A identifies the quotient of ULift A by
the image of I with ULift (A/I); compose this quotient equivalence with the second
constant-sheaf comparison. Naturality of constant sheafification, inverse image,
section-ring reconstruction, and precomposition gives the displayed quotient
square. No finiteness of A or I, or Noetherian hypothesis on the scheme, is used.
-/
theorem discrete_quotient_comparison (X : Scheme.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) :
    let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
    let B := ULift.{u + 1} A
    let K : Ideal B := Ideal.map
      (ULift.ringEquiv : B ≃+* A).symm.toRingHom I
    let R := condensedRingObj (discreteObj A) X
    let S := condensedRingObj (discreteObj (A ⧸ I)) X
    ∃ e : ConstantCompletion.constant J B ≅ smallRing X R,
      ∃ f : ConstantCompletion.finite J B K 0 ≅ smallRing X S,
        ConstantCompletion.quotient J B K 0 ≫ f.hom =
          e.hom ≫ smallMap X (R := R) (S := S)
            ((upperStarFromPoint X).map (discreteMap (Ideal.Quotient.mk I))) := by
  dsimp only
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let B := ULift.{u + 1} A
  let K : Ideal B := Ideal.map (ULift.ringEquiv : B ≃+* A).symm.toRingHom I
  let q : (A ⧸ I) ≃+* (B ⧸ K) :=
    Ideal.quotientEquiv I K (ULift.ringEquiv : B ≃+* A).symm rfl
  let t : (B ⧸ K ^ (0 + 1)) ≃+* ULift.{u + 1} (A ⧸ I) :=
    (Ideal.quotientEquiv _ K (RingEquiv.refl B) (by simp)).trans
      (q.symm.trans ULift.ringEquiv.symm)
  let e := smallIso X A
  let f := (constantSheaf J CommRingCat.{u + 1}).mapIso t.toCommRingCatIso ≪≫
    smallIso X (A ⧸ I)
  refine ⟨e, f, ?_⟩
  change (constantSheaf J CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (0 + 1)))) ≫
      ((constantSheaf J CommRingCat.{u + 1}).map t.toCommRingCatIso.hom ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp]
  have ht : (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (0 + 1)))) ≫
      t.toCommRingCatIso.hom =
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change t (Ideal.Quotient.mk _ b) = _
    change ULift.up (q.symm ((Ideal.quotientEquiv _ K (RingEquiv.refl B) (by simp))
      (Ideal.Quotient.mk _ b))) = _
    rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_symm_mk]
    rfl
  rw [ht]
  exact smallIso_naturality X (Ideal.Quotient.mk I)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
