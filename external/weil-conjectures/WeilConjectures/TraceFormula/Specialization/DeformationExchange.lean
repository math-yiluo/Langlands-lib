/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen
public import WeilConjectures.TraceFormula.Specialization.SupportClosureProper
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.ComponentCounitIso
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF
public import WeilConjectures.Tactic.MatchTactic
public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeAssembly
public import WeilConjectures.TraceFormula.Specialization.PointExchangeNormalForm

/-!

# The compact-support exchanges of the deformation to the normal cone

For a correspondence `c` contracting at `y`, the compact-support exchanges of blueprint
`prose-E-15` (3) for the support map
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`, through
the compactification `C ⊂ C̄ ⟶ X ⨯ X` deformed along `c̄⁻¹(x, x)`) and for the structure map of `X`
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated`, through a compactification
`X ⊂ X̄` and the dense compactification of the deformation of `X̄`) give the trace specialization
`deformationTraceSpecialization`. This file states that these exchanges specialize the class of
the component `B ∋ y` of the fixed locus
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)

private lemma eq_fullSubcategory_hom_to_map {C : Type*} [Category C]
    {P : ObjectProperty C} {A B : P.FullSubcategory} {f : A.obj ⟶ B.obj} {g : A ⟶ B}
    (h : f = g.hom) : f = P.ι.map g := h

private lemma componentSpecialLift_comp_d_deformation
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] {b : RationalPoint B}
    (hb : b ≫ j ≫ F.ι = y) :
    hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d =
      deformationSpecialFibreMap (j ≫ F.d)
        (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k' := by
  rw [← (hc.specialFixedLocus k').ι_c₁, hc.componentSpecialLift_ι_assoc]
  change componentSpecialFibreMap k' j hb ≫ hc.specialLeg₁ k' = _
  rw [deformationSpecialFibreMap_comp k' _ _ _ _
      (map_siteIdeal_ker_le_of_comp_eq _ (by rw [← Category.assoc, hb]))]
  exact deformationSpecialFibreMap_eq_of_eq k' _ _ (by simp only [Category.assoc, F.ι_c₁]) _

private lemma componentSupport_lowerStar_obj_eq
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    R((((j ≫ F.ι).left ≫ (supportClosureι c).left) ≫
      (Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
        (supportClosureMap c ≫ Limits.prod.snd)).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj N.obj =
      ((boundedConstructibleLowerStar ℓ ((j ≫ F.d) ≫ diag X)).obj N).obj := by
  have hphg : ((j ≫ F.ι).left ≫ (supportClosureι c).left) ≫
      (Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
        (supportClosureMap c ≫ Limits.prod.snd)).left = ((j ≫ F.d) ≫ diag X).left :=
    (componentPointModelHom_comp_diag_left (F := F) j).symm
  rw [hphg]
  rfl

private lemma componentSupport_special_lowerStar_obj_eq
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] {b : RationalPoint B}
    (hb : b ≫ j ≫ F.ι = y)
    (N : Dᵇc((deformationSpecialFibre B b.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    R((((componentSpecialFibreMap k' j hb).left ≫ (hc.supportClosureSpecialι k').left) ≫
      (supportClosureSpecialMap c y k').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj N.obj =
      ((boundedConstructibleLowerStar ℓ ((hc.componentSpecialLift k' j hb ≫
        (hc.specialFixedLocus k').d) ≫
          diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))).obj N).obj := by
  have hphg' : ((componentSpecialFibreMap k' j hb).left ≫ (hc.supportClosureSpecialι k').left) ≫
      (supportClosureSpecialMap c y k').left = ((hc.componentSpecialLift k' j hb ≫
        (hc.specialFixedLocus k').d) ≫
          diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')).left := by
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, hc.supportClosureSpecialι_comp k',
      ← hc.componentSpecialLift_ι k' j hb, Category.assoc, (hc.specialFixedLocus k').isPullback.w,
      ← Category.assoc]
  rw [hphg']
  rfl

private lemma diagPushforwardExchange_eq_of_preserves (x : RationalPoint X)
    (hXm : (deformationModel X x.left.ker k').PreservesBoundedConstructible
      (Profinite.padicAlgClRingObj ℓ))
    (hXXm : (deformationProdModel X x.left.ker X x.left.ker k').PreservesBoundedConstructible
      (Profinite.padicAlgClRingObj ℓ)) :
    diagPushforwardExchange ℓ X k' x =
      (deformationDiagModelHom X x.left.ker k').boundedConstructiblePushforwardExchange
        ℓ hXm hXXm := rfl

private lemma supportCompactSupportExchange_component_identity
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsProper j.left]
    {b : RationalPoint B} (hb : b ≫ j ≫ F.ι = y)
    [IsProper (j ≫ F.d).left]
    [IsProper (deformationSpecialFibre B b.left.ker k').hom]
    [IsProper (hc.componentSpecialLift k' j hb).left]
    [IsProper (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d).left] :
    (hc.supportCompactSupportExchange k').app ((boundedConstructibleLowerStar ℓ F.ι).obj
        ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
      (specializationProd (ℓ := ℓ) k' (y ≫ c.c₁)).map
        ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
      (diagPushforwardExchange ℓ X k' (y ≫ c.c₁)).app
          ((boundedConstructibleLowerShriek ℓ F.d).obj
            ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ≫
      (boundedConstructibleLowerStar ℓ
        (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))).map
          ((specialization (ℓ := ℓ) k' (y ≫ c.c₁)).map
            ((boundedConstructibleLowerShriek ℓ F.d).map
                ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _)) ≫
              (boundedConstructibleLowerShriek ℓ F.d).map
                ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app (𝟙_ _)) ≫
              (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j F.d).inv.app (𝟙_ _) ≫
              (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ F.d)).hom.app
                (𝟙_ _)) ≫
            ((componentPointModelHom k' j hb).boundedConstructiblePushforwardExchange
              ℓ
              ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel B _ k')
                (deformationModel_exists_comp_ε B _ k'))
              ((deformationModel X (y ≫ c.c₁).left.ker k')
                |>.preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel X _ k')
                (deformationModel_exists_comp_ε X _ k'))).app (𝟙_ _)) =
      (boundedConstructibleLowerShriek ℓ (hc.specialCorrespondence k').support).map
        ((specialization (ℓ := ℓ) k' y).map
          ((boundedConstructibleLowerStar ℓ F.ι).map
              ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _)) ≫
            (boundedConstructibleLowerStarCompOfEq ℓ j F.ι rfl).hom.app (𝟙_ _)) ≫
          ((componentModelHom k' j hb).boundedConstructiblePushforwardExchange ℓ
              ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel B _ k')
                (deformationModel_exists_comp_ε B _ k'))
              ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k')
                (deformationModel_exists_comp_ε c.C _ k'))).app
            (𝟙_ _) ≫
          (boundedConstructibleLowerStarCompOfEq ℓ (hc.componentSpecialLift k' j hb)
            (hc.specialFixedLocus k').ι (hc.componentSpecialLift_ι k' j hb)).inv.app
              ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
        (lowerStarLowerShriekCompIso ℓ (hc.specialFixedLocus k').isPullback.w).hom.app
          ((boundedConstructibleLowerStar ℓ (hc.componentSpecialLift k' j hb)).obj
            ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
        (boundedConstructibleLowerStar ℓ
          (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))).map
            (((boundedConstructibleLowerShriek ℓ (hc.specialFixedLocus k').d).map
                ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
                  (hc.componentSpecialLift k' j hb)).inv.app
                    ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
              (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (hc.componentSpecialLift k' j hb)
                (hc.specialFixedLocus k').d).inv.app
                  ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _)) ≫
              (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
                (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d)).hom.app
                  ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
              eqToHom (congrArg (fun f ↦ (boundedConstructibleLowerStar ℓ f).obj
                ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _)))
                  (hc.componentSpecialLift_comp_d_deformation k' F j hb))) := by
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have hN := (deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k') (deformationModel_exists_comp_ε c.C _ k')
  have hXm := (deformationModel X (y ≫ c.c₁).left.ker k')
    |>.preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel X _ k') (deformationModel_exists_comp_ε X _ k')
  have hXXm := NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
  have hF1 := supportCompactSupportExchange_app_lowerStar_eq hc k' j hb
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hF3 := componentSupportModelHom_pushforwardExchange_app hc k' j hb
  have : IsProper (j ≫ F.ι).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((j ≫ F.d) ≫ diag X).left := by rw [Over.comp_left]; infer_instance
  have : IsProper ((j ≫ F.ι) ≫ c.support).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((j ≫ F.ι) ≫ supportClosureι c).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (((j ≫ F.ι) ≫ supportClosureι c) ≫ Limits.prod.lift
    (supportClosureMap c ≫ Limits.prod.fst) (supportClosureMap c ≫ Limits.prod.snd)).left :=
    isProper_left_of_isProper_of_isSeparated _
  have hF2 := compactificationRoute_ambient_eq_fixedSquareRoute_of_eq ℓ j (rfl : j ≫ F.ι = _)
    F.isPullback.w (supportClosureι c)
    (Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
      (supportClosureMap c ≫ Limits.prod.snd))
    (by rw [prodLift_supportClosureMap, supportClosureι_map])
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (componentSupport_lowerStar_obj_eq F j
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have : IsProper ((hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d) ≫
    diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb ≫
    (hc.specialCorrespondence k').support).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb ≫ hc.supportClosureSpecialι k').left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((componentSpecialFibreMap k' j hb ≫ hc.supportClosureSpecialι k') ≫
    supportClosureSpecialMap c y k').left := isProper_left_of_isProper_of_isSeparated _
  -- Fix the ambient fibre before instantiating the route, keeping its category parameters uniform.
  have hF2' := compactificationRoute_ambient_eq_fixedSquareRoute_of_eq ℓ
    (C := deformationSpecialFibre c.C y.left.ker k')
    (hc.componentSpecialLift k' j hb) (hc.componentSpecialLift_ι k' j hb)
    (hc.specialFixedLocus k').isPullback.w (hc.supportClosureSpecialι k')
    (supportClosureSpecialMap c y k') (hc.supportClosureSpecialι_comp k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
      (hc.componentSupport_special_lowerStar_obj_eq k' F j hb
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
          (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
  instantiate_by_match eq_fullSubcategory_hom_to_map [h := hF2'] as hF2map
  have hfsp := hc.componentSpecialLift_comp_d_deformation k' F j hb
  have hL := eqToHom_comp_map_lowerStarComp_inv ℓ (j ≫ F.d) (j ≫ F.d) rfl (diag X)
    (componentPointModelHom_comp_diag_left j) (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (componentSupport_lowerStar_obj_eq F j
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have hL' := eqToHom_comp_map_lowerStarComp_inv ℓ
    (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d) _ hfsp
    (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))
    (componentPointModelHom_comp_diag_special hc k' j hb)
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
      (hc.componentSupport_special_lowerStar_obj_eq k' F j hb
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
          (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
  have hχg := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (componentModelHom k' j hb) hM hN
  have hχΔ := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (deformationDiagModelHom X (y ≫ c.c₁).left.ker k') hXm hXXm
  have hχΔ' (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
    (congrArg (fun χ : type_of% (diagPushforwardExchange ℓ X k' (y ≫ c.c₁)) ↦
      (boundedConstructible _).ι.map (χ.app T))
      (diagPushforwardExchange_eq_of_preserves k' (y ≫ c.c₁) hXm hXXm)).trans (hχΔ T)
  have hχdj := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (componentPointModelHom k' j hb) hM hXm
  apply_by_match CategoryTheory.supportIdentity_aux
    [Sp := specialization (ℓ := ℓ) k' y,
    Ts := specializationProd (ℓ := ℓ) k' (y ≫ c.c₁),
    SX := specialization (ℓ := ℓ) k' (y ≫ c.c₁),
    SB := NearbyCyclesModel.boundedConstructibleNearbyCycles hM,
    χΔ := diagPushforwardExchange ℓ X k' (y ≫ c.c₁),
    N₀ := (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧),
    Rι' := boundedConstructibleLowerStar ℓ (hc.specialFixedLocus k').ι,
    Rd' := boundedConstructibleLowerShriek ℓ (hc.specialFixedLocus k').d,
    Ξ' := lowerStarLowerShriekCompIso ℓ (hc.specialFixedLocus k').isPullback.w,
    i₁ := compactificationLowerShriekIso ℓ (hc.supportClosureSpecialι k')
      (supportClosureSpecialMap c y k') (hc.supportClosureSpecialι_comp k'),
    cO' := boundedConstructibleOpenImmersionLowerShriekCompatibility
      (Profinite.padicAlgClRingObj ℓ) ℓ (hc.supportClosureSpecialι k'),
    cR' := boundedConstructibleLowerStarCompatibility ℓ (supportClosureSpecialMap c y k'),
    M' := (boundedConstructibleLowerStar ℓ (hc.componentSpecialLift k' j hb)).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    T' := (boundedConstructibleLowerStar ℓ
      (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d)).obj
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    T₂' := (boundedConstructibleLowerStar ℓ
      ((hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d) ≫
        diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))).obj
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    hχΔ := hχΔ', hχg := hχg, hχdj := hχdj,
    hF2 := hF2, hF2' := hF2map, hL := hL, hL' := hL', hF1 := hF1, hF3 := hF3,
    t := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _),
    hι := (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⨯
        deformationSpecialFibre X (y ≫ c.c₁).left.ker k').left))).faithful,
    hback := NatIso.hom_app_comp_inv_app_comp_map_eqToHom
      (boundedConstructibleLowerStarComp ℓ (j ≫ F.d) (diag X)) (𝟙_ _) rfl,
    cinv := (boundedConstructibleLowerStarCompOfEq ℓ (hc.componentSpecialLift k' j hb)
      (hc.specialFixedLocus k').ι (hc.componentSpecialLift_ι k' j hb)).inv.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    hcinv := Iso.inv_hom_id_app (boundedConstructibleLowerStarCompOfEq ℓ
      (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
        (hc.componentSpecialLift_ι k' j hb))
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    tr := eqToHom (congrArg (fun f ↦ (boundedConstructibleLowerStar ℓ f).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp),
    hback' := NatIso.hom_app_comp_inv_app_comp_map_eqToHom_eq (boundedConstructibleLowerStarComp ℓ
      (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d)
      (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')))
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))
      (congrArg (fun f ↦ (boundedConstructibleLowerStar ℓ f).obj
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)
      (congrArg (fun f ↦ (boundedConstructibleLowerStar ℓ f).obj
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)]

private lemma fixedLocusExchange_component_factorization
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsProper j.left]
    {b : RationalPoint B} (hb : b ≫ j ≫ F.ι = y)
    [IsProper (deformationTotalToTrait B b.left.ker k')]
    [IsProper (hc.componentSpecialLift k' j hb).left] :
    (hc.fixedLocusExchange k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F).app
        ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _)) =
      ((boundedConstructibleLowerShriek ℓ (toPoint (hc.specialFixedLocus k').F)).map
        (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (hc.specialFixedLocus k').ι).map
            ((specialization (ℓ := ℓ) k' y).map
              ((boundedConstructibleLowerStar ℓ F.ι).map
                ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _)) ≫
                (boundedConstructibleLowerStarComp ℓ j F.ι).hom.app (𝟙_ _)) ≫
              ((componentModelHom k' j hb).boundedConstructiblePushforwardExchange
                ℓ
              ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel B _ k')
                (deformationModel_exists_comp_ε B _ k'))
              ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
                (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k')
                (deformationModel_exists_comp_ε c.C _ k'))).app (𝟙_ _) ≫
              (boundedConstructibleLowerStarCompOfEq ℓ (hc.componentSpecialLift k' j hb)
                (hc.specialFixedLocus k').ι (hc.componentSpecialLift_ι k' j hb)).inv.app
                  ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ
              (hc.specialFixedLocus k').ι).counit.app
                ((boundedConstructibleLowerStar ℓ (hc.componentSpecialLift k' j hb)).obj
                ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _)))) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
            (hc.componentSpecialLift k' j hb)).inv.app
              ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
        (lowerShriekCompOfEq ℓ (hc.componentSpecialLift k' j hb)
          (toPoint (hc.specialFixedLocus k').F) (comp_toPoint _)).inv.app
            ((specialization (ℓ := ℓ) k' b).obj (𝟙_ _))) ≫
        (deformationCompactSupportExchange B b.left.ker k').app (𝟙_ _) ≫
        (traitSpecialization k k').map
          ((lowerShriekCompOfEq ℓ j (toPoint F.F) (comp_toPoint j)).hom.app (𝟙_ _)) := by
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have : IsProper (j ≫ F.d).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d).left :=
    isProper_left_of_isProper_of_isSeparated _
  have hSI := hc.supportCompactSupportExchange_component_identity k' F j hb
  have hfsp := hc.componentSpecialLift_comp_d_deformation k' F j hb
  -- fact (II): the factorization of `ν_F` on `j_! ℚ̄_ℓ`
  have : IsProper (deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k').left := by
    rw [← hfsp]; infer_instance
  have hNF := pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm (ℓ := ℓ)
    (y ≫ c.c₁) k' (j ≫ F.d) (component_comp_d_eq j hb)
  instantiate_by_match TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq
    [h := hSI, hX := hNF] as hFPE
  have hS3 := lowerShriekCompOfEq_hom_app_comp_hom_app_comp_map_inv_comp_inv ℓ j F.d
    (toPoint X) (comp_toPoint j) (comp_toPoint F.d) (comp_toPoint (j ≫ F.d))
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hS4 := lowerShriekCompOfEq_hom_app_comp_map_comp_inv_eq ℓ
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').d hfsp (toPoint _)
    (comp_toPoint (hc.componentSpecialLift k' j hb)) (comp_toPoint (hc.specialFixedLocus k').d)
    (comp_toPoint (deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k'))
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))
    (congrArg (fun f ↦ (boundedConstructibleLowerStar ℓ f).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)
  have hac := boundedConstructibleLowerStarCompOfEq_hom_app_rfl ℓ j F.ι
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  dsimp only [fixedLocusExchange]
  apply_by_match CategoryTheory.exchange_app_eq_of_fixedSquare_aux
    [h := hFPE, hS3 := hS3, hS4 := hS4, hac := hac]

set_option Elab.async false in
-- instantiating the support identity, facts (II) and (III) and the reduction at the concrete data
-- is slow; the auxiliary theorems of `instantiate_by_match` are checked one after the other
-- (`Elab.async false`), which keeps the memory below 4 GB
/-- **The compact-support exchanges of the deformation specialize the class of `B`** (blueprint
`corollary-specialization-when-fixed-point-scheme--1`, with
`lemma-fixed-point-scheme-deformation--1`; Varshavsky, *Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2): for the exchanges `ν_c`
(`supportCompactSupportExchange`) and `ν_X` (`pointCompactSupportExchangeOfSeparated`), the
exchange `ν_F` of the fixed loci maps the specialization of the unit class of the special fixed
locus `F'` to the specialization of the class of the component `B ∋ y`. Near `y` the deformed fixed
locus is the constant family `B × S` up to nilpotents, on which `ν` is the inverse of the proper
exchange and is compatible with the specialization units. -/
theorem specializesComponentClass_deformation {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    hc.SpecializesComponentClass k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j := by
  have hmem : (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k)) ∈
      Set.range j.left.base := by rw [hB]; rfl
  obtain ⟨b, hbj, hbr⟩ := RationalPoint.exists_lift_of_range_eq_singleton j
    (F.liftPoint y hc.comp_c₁_eq_comp_c₂) hB
  have hb : b ≫ j ≫ F.ι = y := by rw [← Category.assoc, hbj, FixedLocus.liftPoint_ι]
  have hI := hc.isIso_ΨF_map_componentCounit k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j hmem
  have : IsProper (deformationTotalToTrait B b.left.ker k') :=
    isProper_deformationTotalToTrait_ker B k' hbr
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have hN := (deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k') (deformationModel_exists_comp_ε c.C _ k')
  have : IsProper j.left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (hc.componentSpecialLift k' j hb).left :=
    isProper_left_of_isProper_of_isSeparated _
  have h3 := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
    (hc.componentSpecialLift_ι k' j hb) hI
  have hD := unitClass_comp_map_comp_deformationCompactSupportExchange_app B b.left.ker k' (ℓ := ℓ)
  have h1 := hc.fixedLocusExchange_component_factorization k' F j hb
  -- fact (III) glued to the unit class identity of `ν_B`
  instantiate_by_match CategoryTheory.comp_map_comp_comp_eq_of_eq' [h := h3, h' := hD] as h2
  -- the cancellation
  apply_by_match TraceSpecialization.specializesComponentClass_of_eq [j := j, hI := hI,
    h₁ := h1, h₂ := h2]

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
