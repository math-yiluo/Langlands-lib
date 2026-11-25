/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement

/-! # Signed powers of a line give inverse tensor functors

Source: definition-tate-twists--10, proof steps 1--2.
(blueprint: lem-weil-signed-line-tensor-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u uC vC r
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite MonoidalCategory
namespace PresheafOfModules

section LineUnit

variable {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
  (N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
private noncomputable def line_homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

private lemma line_map_id_apply' {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

private lemma line_homObjUnitInvApp_app_one {U : C} (n : N.obj (op U)) :
    (line_homObjUnitInvApp N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (N.line_map_id_apply' n))

/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
private noncomputable def line_homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ConcreteCategory.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ConcreteCategory.ofHom
        { toFun n := line_homObjUnitInvApp N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                (show N.obj (op W.unop.left) from N.map W.unop.hom.op (n + n')) =
                (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) +
                  (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n')
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                (show N.obj (op W.unop.left) from N.map W.unop.hom.op (r • n)) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n)
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • (show N.obj (op W.unop.left) from
          N.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop)))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact line_homObjUnitInvApp_app_one N n }

/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
private noncomputable def line_homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (line_homObjUnitIsoApp N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm

private noncomputable def lineEvalId
    (M N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)) (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)]
      M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

private noncomputable def lineEval
    (M N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)) :
    SheafOfModules.siteTensorPresheaf M (homObj M N) ⟶ N where
  app X := ModuleCat.ofHom (TensorProduct.lift (lineEvalId M N X.unop).flip)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m φ
    change ((homObj M N).map f φ).app (op (Over.mk (𝟙 Y.unop)))
      (M.map f m) = N.map f (φ.app (op (Over.mk (𝟙 X.unop))) m)
    refine (restrictOver_hom_app_congr φ (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply φ (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

private theorem lineEval_bijective
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)) {W : C}
    (m₀ : M.obj (op W))
    (φ₀ : (restrictOver R W).obj M ⟶ (restrictOver R W).obj (unit _))
    (hφ₀ : φ₀.app (op (Over.mk (𝟙 W))) m₀ = (1 : R.obj (op W)))
    (hgen : ∀ (V : Over W) (x : M.obj (op V.left)),
      ∃ r : R.obj (op V.left), x = r • M.restrictₛₗ V.hom.op m₀) :
    Function.Bijective ((lineEval M (unit _)).app (op W)) := by
  refine TensorProduct.lift_bijective_of_forall_eq_smul
    (lineEvalId M (unit _) W).flip m₀ (fun p ↦ ?_)
    ⟨?_, fun (a : R.obj (op W)) ↦ ⟨a • φ₀, ?_⟩⟩
  · obtain ⟨r, hr⟩ := hgen (Over.mk (𝟙 W)) p
    refine ⟨r, hr.trans (congrArg (r • ·) ?_)⟩
    rw [PresheafOfModules.restrictₛₗ_apply]
    simp
    rfl
  · rw [injective_iff_map_eq_zero]
    intro (q : (restrictOver R W).obj M ⟶ (restrictOver R W).obj (unit _))
      (hq : q.app (op (Over.mk (𝟙 W))) m₀ = 0)
    refine hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨r, rfl⟩ := hgen V.unop x
    have h0 : q.app V (M.restrictₛₗ V.unop.hom.op m₀) = 0 :=
      (naturality_apply q (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op m₀).trans
        ((congrArg _ hq).trans (map_zero _))
    refine ((q.app V).hom.map_smul r _).trans ?_
    rw [h0]
    exact smul_zero _
  · refine (LinearMap.map_smul _ a φ₀).trans ?_
    exact (congrArg (fun y : R.obj (op W) ↦ a • y) hφ₀).trans (mul_one a)

private theorem lineEval_of_inverse
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)) {V : C}
    (φ : (restrictOver R V).obj M ⟶ (restrictOver R V).obj (unit _))
    (ψ : (restrictOver R V).obj (unit _) ⟶ (restrictOver R V).obj M)
    (hi : ∀ (W : (Over V)ᵒᵖ) (r : R.obj (op W.unop.left)),
      φ.app W (ψ.app W r) = r)
    (hi' : ∀ (W : (Over V)ᵒᵖ) (x : M.obj (op W.unop.left)),
      ψ.app W (φ.app W x) = x) :
    Function.Bijective ((lineEval M (unit _)).app (op V)) := by
  let m₀ := ψ.app (op (Over.mk (𝟙 V))) (1 : R.obj (op V))
  refine lineEval_bijective M m₀ φ (hi _ _) ?_
  intro W x
  refine ⟨φ.app (op W) x, ?_⟩
  have hn := naturality_apply ψ
    (Over.homMk W.hom : W ⟶ Over.mk (𝟙 V)).op (1 : R.obj (op V))
  have hone : ((restrictOver R V).obj
      (unit _)).map
      (Over.homMk W.hom : W ⟶ Over.mk (𝟙 V)).op
        (1 : R.obj (op V)) = (1 : R.obj (op W.left)) :=
    unit_map_one _ _
  rw [hone] at hn
  change ψ.app (op W) (1 : R.obj (op W.left)) =
    M.restrictₛₗ W.hom.op m₀ at hn
  calc
    x = ψ.app (op W) (φ.app (op W) x) := (hi' _ _).symm
    _ = (show R.obj (op W.left) from φ.app (op W) x) •
        ψ.app (op W) (1 : R.obj (op W.left)) := by
      rw [← map_smul]
      congr 1
      let a : R.obj (op W.left) := φ.app (op W) x
      change a = a * 1
      exact (mul_one a).symm
    _ = _ := congrArg ((show R.obj (op W.left) from φ.app (op W) x) • ·) hn

end LineUnit

end PresheafOfModules

namespace SheafOfModules

section LineSheaves

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}] in
private theorem lineEval_local
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {U V : C} (e : M.over U ≅ (unit _).over U) (g : V ⟶ U) :
    Function.Bijective ((PresheafOfModules.lineEval M.val (PresheafOfModules.unit _)).app
      (op V)) := by
  let φ : (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj (PresheafOfModules.unit _) :=
    { app W := e.hom.val.app W
      naturality f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (e.hom.val.naturality f) x }
  let ψ : (PresheafOfModules.restrictOver R.obj U).obj (PresheafOfModules.unit _) ⟶
      (PresheafOfModules.restrictOver R.obj U).obj M.val :=
    { app W := e.inv.val.app W
      naturality f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (e.inv.val.naturality f) x }
  let φ' := PresheafOfModules.restrictOverMap g φ
  let ψ' := PresheafOfModules.restrictOverMap g ψ
  have hi (W : (Over V)ᵒᵖ) (r : R.obj.obj (op W.unop.left)) : φ'.app W (ψ'.app W r) = r := by
    have h := congrArg (fun f => (f.val.app
      (op ((Over.map g).obj W.unop))).hom) e.inv_hom_id
    exact LinearMap.congr_fun h r
  have hi' (W : (Over V)ᵒᵖ) (x : M.val.obj (op W.unop.left)) : ψ'.app W (φ'.app W x) = x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.val.app (op ((Over.map g).obj W.unop))) e.hom_inv_id) x
  exact PresheafOfModules.lineEval_of_inverse M.val φ' ψ' hi hi'

private noncomputable def lineEvalIso
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] :
    (siteSheafTensorRight (A := R) (homObj (R := R) M (unit _))).obj M ≅ unit _ := by
  classical
  let f := PresheafOfModules.lineEval M.val (PresheafOfModules.unit _)
  have hw : (J.W.inverseImage (PresheafOfModules.toPresheaf _)) f := by
    obtain ⟨I, U, hc, hU⟩ :=
      (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
        (M := M) (r := 1)).mp inferInstance
    have hb (V : C) (i : I) (g : V ⟶ U i) : Function.Bijective (f.app (op V)) := by
      let e := (hU i).some ≪≫ freeUniqueIso.{u + 1, u, u + 1} _
      exact lineEval_local R M e g
    apply (J.W_iff_isLocallyBijective _).mpr
    exact ⟨Presheaf.isLocallyInjective_of_coversTop hc _ fun V i g ↦ (hb V i g).1,
      Presheaf.isLocallySurjective_of_coversTop hc _ fun V i g ↦ (hb V i g).2⟩
  change (J.W.inverseImage (PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)) f at hw
  have he := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  rw [he, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hw
  let := hw
  exact asIso ((PresheafOfModules.sheafification (𝟙 _)).map f) ≪≫
    sheafificationObjUnitIso R

private noncomputable def lineHomUnitIso
    (N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    homObj (R := R) (unit _) N ≅ N :=
  (fullyFaithfulForget _).preimageIso (PresheafOfModules.line_homObjUnitIso N.val)

private noncomputable def lineOverHomIso
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (U : C) :
    (homObj (R := R) M N).over U ≅ homObj (R := R.over U) (M.over U) (N.over U) := by
  have he : PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
      ((PresheafOfModules.restrictOver R.obj U).obj M.val)
      ((PresheafOfModules.restrictOver R.obj U).obj N.val) =
      PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
        (M.over U).val (N.over U).val := by congr 1
  exact (fullyFaithfulForget _).preimageIso <|
    (Iso.refl _ : ((homObj (R := R) M N).over U).val ≅
      (PresheafOfModules.restrictOver R.obj U).obj (homObj (R := R) M N).val) ≪≫
    PresheafOfModules.restrictOverHomObjIso (R := R.obj) M.val N.val U ≪≫ eqToIso he

private noncomputable def lineTensorCongr
    {M M' N N' : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
    (e : M ≅ M') (f : N ≅ N') :
    (siteSheafTensorRight (A := R) N).obj M ≅
      (siteSheafTensorRight (A := R) N').obj M' := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  exact (siteSheafTensorRightIso R N).app M ≪≫
    MonoidalCategory.tensorIso e f ≪≫ ((siteSheafTensorRightIso R N').app M').symm

private noncomputable def lineTensorUnit
    (N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (siteSheafTensorRight (A := R) (unit _)).obj N ≅ N := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  exact (siteSheafTensorRightIso R (unit _)).app N ≪≫ MonoidalCategory.rightUnitor N

end LineSheaves

end SheafOfModules

namespace WeilConjectures

private noncomputable def linePowerOverUnit (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (U : S.ProEt) (e : L.over U ≅ SheafOfModules.unit
      (((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :
    ∀ n : ℕ, (coefficientTwistPower.{u} S (R := R) L n).over U ≅
      SheafOfModules.unit
      (((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact Iso.refl _
  | one => exact e
  | more n _ ih =>
    let c := (SheafOfModules.exists_localizedSiteTensorRestriction.{u + 1, u, u + 1, u + 1}
      (ProEt.topology S) R U).choose
    exact c (coefficientTwistPower.{u} S (R := R) L (n + 1)) L ≪≫
      SheafOfModules.lineTensorCongr (R.over U) ih e ≪≫
        SheafOfModules.lineTensorUnit (R.over U) _

private noncomputable def lineSignedOverUnit (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (U : S.ProEt) (e : L.over U ≅ SheafOfModules.unit
      (((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))
    (m : ℤ) : (coefficientTwistLine.{u} S (R := R) L m).over U ≅
      SheafOfModules.unit
      (((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U) := by
  cases m with
  | ofNat n => exact linePowerOverUnit S R L U e n
  | negSucc n =>
    exact SheafOfModules.lineOverHomIso R (coefficientTwistPower.{u} S (R := R) L (n + 1)) _ U ≪≫
      ((SheafOfModules.homFunctor (R.over U)).flip.obj (SheafOfModules.unit _)).mapIso
        (linePowerOverUnit S R L U e (n + 1)).symm.op ≪≫
      SheafOfModules.lineHomUnitIso (R.over U) _

private theorem lineSignedRank (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (coefficientTwistLine S (R := R) L m).IsFiniteLocallyFreeOfRank 1 := by
  classical
  obtain ⟨I, U, hc, hU⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
      (M := L) (r := 1)).mp
      inferInstance
  apply (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
    (coefficientTwistLine.{u} S (R := R) L m)).mp
  apply SheafOfModules.isInvertible_of_forall_over_unit.{u + 1, u, u + 1} U hc
  intro i
  let e := (hU i).some ≪≫ SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _
  exact ⟨lineSignedOverUnit S R L (U i) e m⟩

/-- Signed tensor powers remain lines, and opposite powers give inverse sheaf tensor functors.
Source: blueprint definition-tate-twists--10, proof steps 1--2
(blueprint: lem-weil-signed-line-tensor-equivalence).

Proof: choose a cover on which L is the coefficient unit. Tensor powers restrict to
powers of the unit; internal Hom restricts to the Hom of the restrictions, so its
negative powers are units on that same cover. This proves rank one for all signed
powers, including zero. The evaluation pairings identify the positive power tensored
with its internal dual with the unit: locally they are multiplication of coefficients.
For negative exponents the bidual evaluation identifies the other signed power with
that dual, since evaluation is an isomorphism for a rank-one free module. The local
inverses of evaluation glue, since the evaluation map is defined before trivializing.
Associate (M tensor L(m)) tensor L(-m) to M tensor (L(m) tensor L(-m)), apply this
evaluation and the unit isomorphism. These isomorphisms are natural in M, and give
the asserted inverse tensor functors. Empty covering members cause no exception. -/
theorem signedLineTensor_equivalence (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (coefficientTwistLine.{u} S (R := R) L m).IsFiniteLocallyFreeOfRank 1 ∧
      Nonempty (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
          (coefficientTwistLine.{u} S L m) ⋙
        SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
          (coefficientTwistLine.{u} S L (-m)) ≅ 𝟭 _) := by
  classical
  refine ⟨lineSignedRank S R L m, ?_⟩
  let : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} R
  let P : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    coefficientTwistLine.{u} S (R := R) L m
  let Q : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    coefficientTwistLine.{u} S (R := R) L (-m)
  have ev : P ⊗ Q ≅ SheafOfModules.unit
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := by
    cases m with
    | ofNat n =>
      cases n with
      | zero => exact MonoidalCategory.leftUnitor _
      | succ n =>
        have : (coefficientTwistPower S (R := R) L (n + 1)).IsFiniteLocallyFreeOfRank 1 :=
          lineSignedRank S R L (Int.ofNat (n + 1))
        exact ((SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R _).app _).symm ≪≫
          SheafOfModules.lineEvalIso.{u} R _
    | negSucc n =>
      have : (coefficientTwistPower S (R := R) L (n + 1)).IsFiniteLocallyFreeOfRank 1 :=
        lineSignedRank S R L (Int.ofNat (n + 1))
      exact (CategoryTheory.BraidedCategory.braiding _ _) ≪≫
        ((SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R _).app _).symm ≪≫
          SheafOfModules.lineEvalIso.{u} R _
  let C := SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have h : tensorRight P ⋙ tensorRight Q ≅ 𝟭 C :=
    (MonoidalCategory.tensorRightTensor P Q).symm ≪≫
      (MonoidalCategory.tensoringRight C).mapIso ev ≪≫ rightUnitorNatIso C
  exact ⟨Functor.isoWhiskerRight
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R P) _ ≪≫
    Functor.isoWhiskerLeft _
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R Q) ≪≫ h⟩

end WeilConjectures
