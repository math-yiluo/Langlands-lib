/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement

/-! # Fixed-scalar coordinates of finite adic exchange

Source: Stacks Tag 07A7; blueprint finite pro-etale smooth base change, coefficient
realization in the last proof step.
(blueprint: lem-sbc-adic-finite-exchange-encoding).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem whisker_commute
    {C D F G : Type*} [Category C] [Category D] [Category F] [Category G]
    (L : C ⥤ D) (R : F ⥤ G) {P Q : D ⥤ F} (t : P ⟶ Q) :
    Functor.whiskerLeft L (Functor.whiskerRight t R) =
      Functor.whiskerRight (Functor.whiskerLeft L t) R := rfl

private theorem finiteScalars_constantUnit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionScalars W d n = Functor.whiskerRight
      (toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
        (pbcLevelConstantComparison W d n).hom.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)
  have he : Functor.whiskerRight (toSheafify (ProEt.topology W)
        (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
        AdicCoefficients.finiteRingUnit W (ProEtale.PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists W
      (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have hconst : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom =
        AdicCoefficients.constants W (ProEtale.PbcQuotient d n) ≫
          toSheafify (ProEt.topology W)
            (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)) := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  rw [hconst]
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ↦ f.hom)
    e.inv_hom_id
  change (ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) ≫
    e.inv.hom) ≫ e.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  rw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

private theorem finiteDirectImage_adjunct
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    proEtaleRingDirectImageMap f ((pbcAdicRings V d).obj (op n))
      ((pbcAdicRings U d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)) =
        (pbcLevelConstantComparison V d n).inv ≫
          proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of (ProEtale.PbcQuotient d n)) ≫
          (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            (pbcLevelConstantComparison U d n).hom := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change adj.homEquiv _ _ (completedFiniteCoefficientMap f d n) = _
  unfold completedFiniteCoefficientMap
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold proEtaleConstantInverseImageMap
  rw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  rfl

private theorem finiteScalars_directImage
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    pbcFunctionScalars V d n ≫
        Functor.whiskerRight
          (proEtaleRingDirectImageMap f ((pbcAdicRings V d).obj (op n))
            ((pbcAdicRings U d).obj (op n))
            (asIso (completedFiniteCoefficientMap f d n))).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange f).op (pbcFunctionScalars U d n) := by
  rw [finiteScalars_constantUnit, finiteScalars_constantUnit,
    ← Functor.whiskerRight_comp]
  rw [whisker_commute]
  apply congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  rw [finiteDirectImage_adjunct]
  change (toSheafify (ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison V d n).hom.hom) ≫
        ((pbcLevelConstantComparison V d n).inv.hom ≫
          (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of (ProEtale.PbcQuotient d n))).hom ≫
          Functor.whiskerLeft (proEtaleBaseChange f).op
            (pbcLevelConstantComparison U d n).hom.hom) = _
  have hi : (pbcLevelConstantComparison V d n).hom.hom ≫
      (pbcLevelConstantComparison V d n).inv.hom = 𝟙 _ := congrArg
    (fun g : adicLisseConstantRing V (ProEtale.PbcQuotient d n) ⟶
      adicLisseConstantRing V (ProEtale.PbcQuotient d n) ↦ g.hom)
    (pbcLevelConstantComparison V d n).hom_inv_id
  rw [Category.assoc, ← Category.assoc (pbcLevelConstantComparison V d n).hom.hom,
    hi, Category.id_comp, ← Category.assoc]
  have hc := ((sheafificationAdjunction (ProEt.topology V)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ProEtale.PbcQuotient d n))))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n)))))
  change toSheafify (ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ProEtale.PbcQuotient d n))).hom = _ at hc
  rw [hc]
  rfl

private noncomputable def scalarEmbedding (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt (ProEtale.PbcQuotient d n)

private noncomputable def coefficientRestriction (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  SheafOfModules.forget.{u + 1} ((adicLisseForget T).obj
    ((pbcAdicRings T d).obj (op n))) ⋙
    PresheafOfModules.restrictScalars.{u + 1} (pbcFunctionScalars T d n)

private noncomputable def coefficientUnitIso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    scalarEmbedding T d n ≅ pbcFunctionRealization T d n ⋙
      coefficientRestriction T d n := by
  have hunit (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n))) :
      IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (pbcFunctionScalars T d n)).unit.app ((scalarEmbedding T d n).obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) AddCommGrpCat.{u + 1})).obj
        F).property
  let η : scalarEmbedding T d n ⟶
      (scalarEmbedding T d n ⋙
        PresheafOfModules.sheafification.{u + 1} (pbcFunctionScalars T d n)) ⋙
          coefficientRestriction T d n :=
    Functor.whiskerLeft (scalarEmbedding T d n)
      (PresheafOfModules.sheafificationAdjunction.{u + 1} (pbcFunctionScalars T d n)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  exact asIso η

private noncomputable def restrictionDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    proEtaleRingModuleDirectImage f ((pbcAdicRings Y d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)) ⋙
        coefficientRestriction Y d n ≅
      coefficientRestriction X d n ⋙
        PresheafOfModules.pushforward₀ (Scheme.proEtaleBaseChange f)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ProEtale.PbcQuotient d n))) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := ((proEtaleRingModuleDirectImage f ((pbcAdicRings Y d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)) ⋙
        coefficientRestriction Y d n).obj M)
    let R := ((coefficientRestriction X d n ⋙
      PresheafOfModules.pushforward₀ (Scheme.proEtaleBaseChange f)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ProEtale.PbcQuotient d n)))).obj M)
    change L ≅ R
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let g : L.obj U ≃ₗ[ProEtale.PbcQuotient d n] R.obj U :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r m
            have h := congrArg (fun t ↦ (t.app U).hom r) (finiteScalars_directImage d f n)
            change (((proEtaleRingDirectImageMap f ((pbcAdicRings Y d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)))).hom.app U)
              ((pbcFunctionScalars Y d n).app U r) •
                (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m) =
                (pbcFunctionScalars X d n).app
                  ((Scheme.proEtaleBaseChange f).op.obj U) r •
                    (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m)
            exact congrArg (fun a : (((adicLisseForget X).obj ((pbcAdicRings X d).obj (op
              n)))).obj.obj
              ((Scheme.proEtaleBaseChange f).op.obj U) ↦ a •
                (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m)) h }
      exact g.toModuleIso
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

/-- Realization commutes with ordinary direct image through the specified scalar map.
Source: Stacks Project, sites-modules.tex, lemma-sheafification-presheaf-modules
and definition-pushforward; blueprint proper finiteness, proof step 2.
(blueprint: lem-weil-pbc-finite-coefficient-realization-direct-image)

Proof: restrict both module actions along constant scalar sections. The realization
unit identifies each underlying sheaf with the original fixed-ring module sheaf.
Both direct images evaluate on the same fibre product, with the same restriction
maps. The coefficient map is precomposition of continuous functions along its
projection, so on constant scalars it is the identity on the coefficient ring.
The identity on these sections is therefore linear for constant scalars. Every
continuous scalar function is locally constant, and sheaf gluing extends this
linearity to the sheafified coefficient ring. It gives a natural isomorphism,
whose inverse is the same identity in the opposite presentation. The construction
also applies to the empty scheme and zero ring. -/
private theorem pbcFunctionRealization_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Nonempty (pbcFunctionRealization X d n ⋙ proEtaleRingModuleDirectImage f ((pbcAdicRings Y
      d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)) ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f ⋙
        pbcFunctionRealization Y d n) := by
  let P := PresheafOfModules.pushforward₀ (Scheme.proEtaleBaseChange f)
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ProEtale.PbcQuotient d n)))
  have h : (coefficientRestriction Y d n).Full := by
    exact (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (pbcFunctionScalars Y d n)).fullyFaithfulROfIsIsoCounit.full
  have h' : (coefficientRestriction Y d n).Faithful := by
    exact (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (pbcFunctionScalars Y d n)).fullyFaithfulROfIsIsoCounit.faithful
  let e : (pbcFunctionRealization X d n ⋙ proEtaleRingModuleDirectImage f ((pbcAdicRings Y
    d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n))) ⋙
        coefficientRestriction Y d n ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f ⋙
        pbcFunctionRealization Y d n) ⋙
        coefficientRestriction Y d n :=
    (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft (pbcFunctionRealization X d n)
        (restrictionDirectImageIso f d n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (coefficientUnitIso X d n).symm P ≪≫
      (Iso.refl _ : scalarEmbedding X d n ⋙ P ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f ⋙ scalarEmbedding Y
          d n) ≪≫
      Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f)
        (coefficientUnitIso Y d n) ≪≫ (Functor.associator _ _ _).symm
  exact ⟨Functor.fullyFaithfulCancelRight (coefficientRestriction Y d n) e⟩

private theorem finitePullbackCoordinates
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃ j : ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f ⋙
        pbcFunctionRealization X d n ≅
      pbcFunctionRealization Y d n ⋙
        proEtaleRingModulePullback f ((pbcAdicRings Y d).obj (op n))
          ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)),
      ∀ (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)))
        (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)))
        (t : (ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f).obj M ⟶ N),
        (proEtaleRingModuleAdjunction f ((pbcAdicRings Y d).obj (op n))
          ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n))).homEquiv
            ((pbcFunctionRealization Y d n).obj M) ((pbcFunctionRealization X d n).obj N)
            (j.inv.app M ≫ (pbcFunctionRealization X d n).map t) =
          (pbcFunctionRealization Y d n).map
            ((ProEtale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f).homEquiv M N t) ≫
          (pbcFunctionRealization_directImage f d n).some.inv.app N := by
  let eY := (pbcFunctionRealization Y d n).asEquivalence
  let eX := (pbcFunctionRealization X d n).asEquivalence
  obtain ⟨j, _, _, hj, _, _⟩ := exists_equivalenceAdjunctionComparison eY eX
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f)
    (proEtaleRingModuleAdjunction f ((pbcAdicRings Y d).obj (op n))
      ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n)))
    (pbcFunctionRealization_directImage f d n).some.symm
  exact ⟨j, hj⟩

end WeilConjectures
