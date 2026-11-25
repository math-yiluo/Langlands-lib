/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # Tensor comparison for invertible coefficient pushforward

Source: Stacks Project, Tag 03EK.
(blueprint: lem-sf-open-coefficient-tensor-pushforward).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory Opposite
namespace WeilConjectures.OpenSemilinearTensor
open WeilConjectures.SemilinearSections SheafOfModules SheafOfModules.ScalarHomOrdinary
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory

section Transport
universe c v d z r
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{z} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {F : C ⥤ D} [hF : F.IsContinuous J K] [hFc : F.IsCocontinuous J K]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (a : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} J K).obj S) [ha : IsIso a]

private abbrev ringMap :
    (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R ⟶
      (F.sheafPushforwardContinuous RingCat.{r} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a

omit [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [F.IsCocontinuous J K] in
private theorem ringMap_app_isIso (V : Cᵒᵖ) :
    IsIso ((ringMap R S a).hom.app V) := by
  let : IsIso a.hom := by
    change IsIso ((sheafToPresheaf J CommRingCat.{r}).map a)
    infer_instance
  change IsIso ((forget₂ CommRingCat.{r} RingCat.{r}).map (a.hom.app V))
  infer_instance

private abbrev push := SheafOfModules.pushforward.{r} (F := F)
  (J := J) (K := K) (ringMap R S a)

private def tensorPush (M N : scalarModules K S) :
    (SheafOfModules.monoidalCategory R).tensorObj ((push R S a).obj M)
      ((push R S a).obj N) ≅
    (push R S a).obj ((SheafOfModules.monoidalCategory S).tensorObj M N) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.isMonoidal_W_independentCoefficients S
  let φ := ringMap R S a
  let P := PresheafOfModules.Monoidal.tensorObj (R := S.obj) M.val N.val
  let e := restrictionTensorPresheafIso φ.hom
    (fun V ↦ ringMap_app_isIso R S a V) M.val N.val
  let q := restrictionSheafificationMap (F := F) (K := J) (L := K) φ P
  have hq : IsIso q :=
    restrictionSheafificationMap_isIso (F := F) (K := J) (L := K) φ P
  exact SheafOfModules.tensorObjIsoSheafification
      ((push R S a).obj M) ((push R S a).obj N) ≪≫
    (PresheafOfModules.sheafification.{r} (R :=
      (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) (𝟙 _)).mapIso e ≪≫
    @asIso _ _ _ _ q hq ≪≫
      (push R S a).mapIso (SheafOfModules.tensorObjIsoSheafification M N).symm

private theorem tensorPush_pure (M N : scalarModules K S) (V : Cᵒᵖ)
    (x : M.val.obj (F.op.obj V)) (y : N.val.obj (F.op.obj V)) :
    (tensorPush R S a M N).hom.val.app V
      (pure R ((push R S a).obj M) ((push R S a).obj N) V x y) =
    pure S M N (F.op.obj V) x y := by
  let φ := ringMap R S a
  let P := PresheafOfModules.Monoidal.tensorObj (R := S.obj) M.val N.val
  let Q := PresheafOfModules.Monoidal.tensorObj (R := R.obj)
    ((push R S a).obj M).val ((push R S a).obj N).val
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let T := SheafOfModules.tensorObjIsoSheafification
    ((push R S a).obj M) ((push R S a).obj N)
  let Z := SheafOfModules.tensorObjIsoSheafification M N
  unfold tensorPush
  exact (tensorComparison_unit_apply φ P Q
    (restrictionTensorPresheafIso φ.hom (fun V ↦ ringMap_app_isIso R S a V) M.val N.val).hom
    T Z V (x ⊗ₜ[R.obj.obj V] y)).trans
    (congrArg (fun z ↦ Z.inv.val.app (F.op.obj V)
      (((PresheafOfModules.sheafificationAdjunction.{r}
        (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
        (𝟙 _)).unit.app P).app
        (F.op.obj V) z))
      (restrictionTensorPresheafIso_pure φ.hom (fun V ↦ ringMap_app_isIso R S a V)
        M.val N.val V x y))

private theorem tensorPush_naturality {M M' N N' : scalarModules K S}
    (f : M ⟶ M') (g : N ⟶ N') :
    (SheafOfModules.monoidalCategory R).tensorHom
        ((push R S a).map f) ((push R S a).map g) ≫ (tensorPush R S a M' N').hom =
      (tensorPush R S a M N).hom ≫ (push R S a).map
        ((SheafOfModules.monoidalCategory S).tensorHom f g) := by
  apply pure_hom_ext R _ _ _
  intro V x y
  let k := (SheafOfModules.monoidalCategory S).tensorHom f g
  change (tensorPush R S a M' N').hom.val.app V
      (((SheafOfModules.monoidalCategory R).tensorHom
        ((push R S a).map f) ((push R S a).map g)).val.app V
          (pure R _ _ V x y)) =
    ((push R S a).map k).val.app V
      ((tensorPush R S a M N).hom.val.app V (pure R _ _ V x y))
  have hR := ScalarHomOrdinary.pure_map R ((push R S a).map f) ((push R S a).map g)
    V x y
  have hS := ScalarHomOrdinary.pure_map S f g (F.op.obj V) x y
  exact (congrArg ((tensorPush R S a M' N').hom.val.app V) hR).trans
    ((tensorPush_pure R S a M' N' V _ _).trans
      (hS.symm.trans (congrArg (k.val.app (F.op.obj V))
        (tensorPush_pure R S a M N V x y).symm)))

private def tensorPushNatIso :
    (push R S a).prod (push R S a) ⋙
        @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) ≅
      @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory S) ⋙ push R S a :=
  NatIso.ofComponents (fun M ↦ tensorPush R S a M.1 M.2) (by
    intro M N f
    exact tensorPush_naturality R S a f.1 f.2)

end Transport

section TensorSite
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (A : Sheaf J CommRingCat.{r})

omit [EssentiallySmall.{r} C] in
private theorem siteFirst_pure {M M' N : scalarModules J A} (f : M ⟶ M')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((siteSheafTensorRight N).map f).val.app V (siteSheafTensorTmul M N V x y) =
      siteSheafTensorTmul M' N V (f.val.app V x) y := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A) (𝟙 _)).unit.naturality
      (siteTensorHom f.val N.val)
  exact (congrArg (fun k ↦ k.app V (x ⊗ₜ[A.obj.obj V] y)) h).symm

omit [EssentiallySmall.{r} C] in
private theorem siteSecond_pure {M N N' : scalarModules J A} (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (siteSheafTensorSecondMap M g).val.app V (siteSheafTensorTmul M N V x y) =
      siteSheafTensorTmul M N' V x (g.val.app V y) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A) (𝟙 _)).unit.naturality
      (siteTensorSecondMap M.val g.val)
  exact (congrArg (fun k ↦ k.app V (x ⊗ₜ[A.obj.obj V] y)) h).symm

private theorem tensorIsoSite_naturality
    {M M' N N' : scalarModules J A} (f : M ⟶ M') (g : N ⟶ N') :
    (SheafOfModules.monoidalCategory A).tensorHom f g ≫ (tensorIsoSite A M' N').hom =
      (tensorIsoSite A M N).hom ≫ (SheafOfModules.siteSheafTensorRight N).map f ≫
        SheafOfModules.siteSheafTensorSecondMap M' g := by
  apply pure_hom_ext A _ _ _
  intro V x y
  change (tensorIsoSite A M' N').hom.val.app V
      (((SheafOfModules.monoidalCategory A).tensorHom f g).val.app V
        (pure A _ _ V x y)) =
    (SheafOfModules.siteSheafTensorSecondMap M' g).val.app V
      (((SheafOfModules.siteSheafTensorRight N).map f).val.app V
        ((tensorIsoSite A M N).hom.val.app V (pure A _ _ V x y)))
  calc
    _ = siteSheafTensorTmul M' N' V (f.val.app V x) (g.val.app V y) :=
      (congrArg ((tensorIsoSite A M' N').hom.val.app V)
        (ScalarHomOrdinary.pure_map A f g V x y)).trans (tensorIsoSite_pure A M' N' V _ _)
    _ = (siteSheafTensorSecondMap M' g).val.app V
        (((siteSheafTensorRight N).map f).val.app V (siteSheafTensorTmul M N V x y)) :=
      ((congrArg ((siteSheafTensorSecondMap M' g).val.app V) (siteFirst_pure A f V x y)).trans
        (siteSecond_pure A g V _ y)).symm
    _ = _ := congrArg (fun z ↦ (siteSheafTensorSecondMap M' g).val.app V
      (((siteSheafTensorRight N).map f).val.app V z)) (tensorIsoSite_pure A M N V x y).symm

private def siteTensorFunctor : scalarModules J A × scalarModules J A ⥤ scalarModules J A
    where
  obj M := (siteSheafTensorRight (A := A) M.2).obj M.1
  map {M N} f := (tensorIsoSite A M.1 M.2).inv ≫
    (SheafOfModules.monoidalCategory A).tensorHom f.1 f.2 ≫ (tensorIsoSite A N.1 N.2).hom
  map_id M := by
    change (tensorIsoSite A M.1 M.2).inv ≫
      (@MonoidalCategory.tensor _ _ (monoidalCategory A)).map (𝟙 M) ≫
        (tensorIsoSite A M.1 M.2).hom = _
    rw [CategoryTheory.Functor.map_id]
    change (tensorIsoSite A M.1 M.2).inv ≫
      𝟙 ((monoidalCategory A).tensorObj M.1 M.2) ≫ (tensorIsoSite A M.1 M.2).hom = _
    simp only [Category.id_comp, Iso.inv_hom_id]
  map_comp {M N P} f g := by
    change (tensorIsoSite A M.1 M.2).inv ≫
      (@MonoidalCategory.tensor _ _ (monoidalCategory A)).map (f ≫ g) ≫
        (tensorIsoSite A P.1 P.2).hom = _
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl

private theorem siteTensorFunctor_map {M M' N N' : scalarModules J A}
    (f : M ⟶ M') (g : N ⟶ N') :
    (siteTensorFunctor A).map (X := (M, N)) (Y := (M', N')) (f, g) =
      (siteSheafTensorRight N).map f ≫
      siteSheafTensorSecondMap M' g := by
  unfold siteTensorFunctor
  apply (cancel_epi (tensorIsoSite A M N).hom).mp
  change (tensorIsoSite A M N).hom ≫ (tensorIsoSite A M N).inv ≫
      (monoidalCategory A).tensorHom f g ≫ (tensorIsoSite A M' N').hom = _
  rw [Iso.hom_inv_id_assoc]
  exact tensorIsoSite_naturality A f g

private def tensorToSite :
    @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory A) ≅ siteTensorFunctor A :=
  NatIso.ofComponents (fun M ↦ tensorIsoSite A M.1 M.2) (by
    intro M N f
    dsimp only [siteTensorFunctor, MonoidalCategory.tensor]
    simp only [Iso.hom_inv_id_assoc])

end TensorSite

end WeilConjectures.OpenSemilinearTensor
