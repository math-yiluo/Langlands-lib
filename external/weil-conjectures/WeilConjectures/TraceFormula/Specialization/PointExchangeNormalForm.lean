/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension
public import WeilConjectures.TraceFormula.Specialization.DeformationUnitClass
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponentBdc
public import WeilConjectures.TraceFormula.Specialization.PointExchangeNormalFormAux
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.Tactic.FirstOrderApply

/-!

# The exchange `ν_X` on a proper component, in normal form

Let `x` be a rational point of a separated `k`-scheme `X` of finite type and `g : B ⟶ X` a
morphism from a proper `k`-scheme `B` with a rational point `b` such that `b ≫ g = x`. On
`Rg_* ℚ̄_ℓ`, the compact-support exchange `ν_X = pointCompactSupportExchangeOfSeparated`, read
through `Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_{B!}`, is the pushforward exchange `χ_g` of the
deformation models followed by `Ra_{X'!} Rg''_* ≅ Ra_{X'!} Rg''_! ≅ Ra_{B''!}` and the inverse
proper exchange `ν_B` of the deformation of `B` (`deformationCompactSupportExchange`)
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] isIso_traitSpecializationUnit

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (x : RationalPoint X) (k' : Type u) [Field k']
  [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] {b : RationalPoint B}
  [IsProper (deformationTotalToTrait B b.left.ker k')] (g : B ⟶ X) (hbg : b ≫ g = x)
  [IsProper g.left]
  [IsProper (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k').left]

/-- **`ν_X` on a proper component, in normal form**: on `Rg_* ℚ̄_ℓ` for `g : B ⟶ X` from a proper
`B` with `b ≫ g = x`, the exchange `ν_X` followed by `Ψ_s(Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_{B!})`
is `Ra_{X'!}(χ_g)` followed by `Ra_{X'!} Rg''_* ≅ Ra_{X'!} Rg''_! ≅ Ra_{B''!}` and the inverse
proper exchange `ν_B` of the deformation of `B`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm :
    (pointCompactSupportExchangeOfSeparated (ℓ := ℓ) x k').app
        ((boundedConstructibleLowerStar ℓ g).obj (𝟙_ _)) ≫
      (traitSpecialization k k').map
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
          (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app (𝟙_ _)) =
    (boundedConstructibleLowerShriek ℓ (toPoint (deformationSpecialFibre X x.left.ker k'))).map
        (((pointComponentModelHom k' g hbg).boundedConstructiblePushforwardExchange ℓ
            ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel B b.left.ker k')
              (deformationModel_exists_comp_ε B _ k'))
            ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel X x.left.ker k')
              (deformationModel_exists_comp_ε X _ k'))).app (𝟙_ _)) ≫
      ((boundedConstructibleLowerShriek ℓ (toPoint (deformationSpecialFibre X x.left.ker k'))).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
            (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')).inv.app _) ≫
        (lowerShriekCompOfEq ℓ
          (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
          (toPoint (deformationSpecialFibre X x.left.ker k')) (comp_toPoint _)).inv.app _ ≫
        (deformationCompactSupportExchange B b.left.ker k').app (𝟙_ _)) := by
  have hF1 := pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq (ℓ := ℓ) x k' g
    hbg (𝟙_ _)
  have hMB := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B b.left.ker k')
    (deformationModel_exists_comp_ε B b.left.ker k')
  have hMS := (traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
    (isTraitModel_traitModel k k') ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩
  have hχg := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
    (pointComponentModelHom k' g hbg) hMB (preservesBoundedConstructible_deformationModel k' X x)
    (𝟙_ _)
  have hχa := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
    (deformationToTraitModelHom B b.left.ker k') hMB hMS (𝟙_ _)
  have : IsProper (g ≫ (compactificationOverField (toPoint X)).overI).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (g ≫ toPoint X).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((g ≫ (compactificationOverField (toPoint X)).overI) ≫
      toPoint (compactificationOverField (toPoint X)).overObj).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have g1 := congrArg R(((toPoint (compactificationOverField (toPoint X)).overObj).left)_*⟦
    Profinite.padicAlgClRingObj ℓ⟧).map (closedExtension_id_app_of_eq
      (Λ := Profinite.padicAlgClRingObj ℓ)
      (g.left ≫ (compactificationOverField (toPoint X)).overI.left) rfl (Category.comp_id _)
      ((boundedConstructible _).ι.obj (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
  have g2 := map_eqToHom_comp_lowerStarCompOfEq_inv_app (Λ := Profinite.padicAlgClRingObj ℓ)
    (Category.comp_id (g.left ≫ (compactificationOverField (toPoint X)).overI.left)).symm
    (toPoint (compactificationOverField (toPoint X)).overObj).left
    ((boundedConstructible _).ι.obj (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have g3 := compactificationRoute_ambient ℓ g (compactificationOverField (toPoint X)).overI
    (toPoint _) (comp_toPoint _) (𝟙_ _)
    (openProperExtension_unit_comp_closedBaseChange ℓ g _ (𝟙_ _))
  have g4 := compactificationRoute_toPoint_eq_normalForm ℓ g
    (compactificationOverField (toPoint X)).overI (𝟙_ _)
  have g5 := isoTrans_isoWhiskerLeft_hom_app
    (lowerShriekCompOfEq ℓ (compactificationOverField (toPoint X)).overI (toPoint _)
      (comp_toPoint _))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      (compactificationOverField (toPoint X)).overI)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint (compactificationOverField (toPoint X)).overObj))
    ((boundedConstructibleLowerStar ℓ g).obj (𝟙_ _))
  have g7 : (boundedConstructibleLowerStarCompatibility ℓ (toPoint B)).hom.app (𝟙_ _) = 𝟙 _ := rfl
  fo_have hG := genericRoute_aux using g5, g1, g3, g2, g4, g7, _
  case hg =>
    rw [pointCompModelHom_pointComponentModelHom_left]
    rfl
  have : IsProper (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k').left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k').left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k') ≫
      toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      toPoint (deformationSpecialFibre (compactificationOverField (toPoint X)).overObj
        (Hom.ker (x ≫ (compactificationOverField (toPoint X)).overI).left) k')).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
      (x ≫ (compactificationOverField (toPoint X)).overI) k')).left := by
    rw [toPoint_left]
    infer_instance
  have : IsProper (toPoint (deformationSpecialFibre B b.left.ker k')).left := by
    rw [toPoint_left]
    infer_instance
  have s1 := closedExtension_app_eq_openProperExtension' ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have s2 := closedExtension_app_eq_openProperExtension' ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have s3 := boundedConstructibleLowerStarComp_inv_app_hom ℓ
    ((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')
    (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k'))
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have T1 := compactificationRoute_toPoint_eq_normalForm ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have hassoc := lowerShriekComp_hom_app_comp_map_inv_comp_inv ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (toPoint (deformationSpecialFibre (compactificationOverField (toPoint X)).overObj
        (Hom.ker (x ≫ (compactificationOverField (toPoint X)).overI).left) k'))
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have htrans := eqToHom_map_comp_lowerShriekComp_inv_app ℓ
    (f := deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (comp_toPoint (pointSpecialMap x (compactificationOverField (toPoint X)).overI k'))
    (𝟙 ((boundedConstructibleLowerShriek ℓ
      (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))))
  have hO1 := openProperExtension_hom_app_eq ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hMB).obj (𝟙_ _))
  have hlc1 := lowerShriekCompOfEq_eq_trans ℓ
    (pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (toPoint (deformationSpecialFibre (compactificationOverField (toPoint X)).overObj
        (Hom.ker (x ≫ (compactificationOverField (toPoint X)).overI).left) k')) (comp_toPoint _)
  have hlcg := lowerShriekCompOfEq_eq_trans ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (toPoint (deformationSpecialFibre X x.left.ker k')) (comp_toPoint _)
  have hlcg1 := lowerShriekCompOfEq_eq_trans ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (toPoint (deformationSpecialFibre (compactificationOverField (toPoint X)).overObj
        (Hom.ker (x ≫ (compactificationOverField (toPoint X)).overI).left) k')) (comp_toPoint _)
  have hF3 := NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq _
    (pointCompModelHom x (compactificationOverField (toPoint X)).overI k'
      (pointComponentModelHom k' g hbg))
    (deformationToTraitModelHom B b.left.ker k')
    (pointCompModelHom_pointComponentModelHom_left (compactificationOverField (toPoint X)).overI g)
    (pointCompModelHom_pointComponentModelHom_special x
      (compactificationOverField (toPoint X)).overI k' g hbg)
    (pointCompModelHom_pointComponentModelHom_total x _ k' g hbg)
    (pointCompModelHom_pointComponentModelHom_generic x _ k' g hbg)
    ((boundedConstructible _).ι.obj (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have hmor : (((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k').left ≫
      (pointSpecialMap x (compactificationOverField (toPoint X)).overI k').left) ≫
      (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k').left) ≫
      (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')).left =
      (toPoint (deformationSpecialFibre B b.left.ker k')).left := by
    simp only [← Over.comp_left, comp_toPoint]
  have hnat := functor_map_comp_eqToHom_of_eq
    (congrArg (fun f ↦ R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧)) hmor)
    ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hMB).hom.app (𝟙_ _))
  have hχiso :=
    NearbyCyclesModel.Hom.isIso_boundedConstructiblePushforwardExchange_of_isProper
      (φ := deformationToTraitModelHom B b.left.ker k') hMB hMS
      (isTraitModel_deformationModel B _ k') (isPullback_deformationSpecialFibre_toPoint B _ k')
      (isPullback_deformationModel_ε_toPoint B _ k')
  fo_apply pointExchange_normalForm_aux using _, _, _, _, _, _, _, _, _, hχiso, _, _,
    _, _, _, _, _, _, _, _, _, _, _, hnat, hχa, hF3, _, hG, _, _, _, _, _, _, _, hχg, _, _, _, _,
    _, hF1, _
  case hS =>
    fo_apply specialRoute_aux using s1, s2, s3, _, _
    case s6 =>
      fo_apply specialNormalForm_aux using hlc1, hlcg, hlcg1, _, hO1, T1, hassoc, htrans
  case hνB => rfl
  case hι => infer_instance
  case hI => infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
