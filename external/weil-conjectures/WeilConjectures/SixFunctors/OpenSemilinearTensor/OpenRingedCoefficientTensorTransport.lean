/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientTensorPushforward
import all WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientTensorPushforward
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # Normalized open tensor transport over abstract coefficient sheaves

Source: Stacks 03DI, 03EK and 0E8I.
(blueprint: lem-sf-open-ringed-coefficient-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.OpenSemilinearTensor
open SheafOfModules SheafOfModules.ScalarHomOrdinary
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory

variable {C : Type c} [Category.{v} C] {D : Type c} [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify K AddCommGrpCat.{max c v r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (W : C)
  [HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [(J.over W).HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (S : Sheaf K CommRingCat.{max c v r}) {F : Over W ⥤ D}
  [hF : F.IsContinuous (J.over W) K] [hFc : F.IsCocontinuous (J.over W) K]
  (a : R.over W ⟶ (F.sheafPushforwardContinuous CommRingCat.{max c v r}
    (J.over W) K).obj S) [ha : IsIso a]
  (I : scalarModules K S ≌ scalarModules (J.over W) (R.over W))
  (η : I.functor ≅ SheafOfModules.pushforward.{max c v r} (F := F)
    (J := J.over W) (K := K)
    ((sheafCompose (J.over W) (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a))

private abbrev sliceExtension := localizedSystemExtension.{c, v, r} R W
private abbrev sliceRestriction := localizedSystemRestriction.{c, v, r} R W

private def sliceRestrictedSection (N : scalarModules J R) (V : C) (b : V ⟶ W)
    (y : ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N).val.obj (op (F.obj (Over.mk b)))) :
    N.val.obj (op V) :=
  (I.counitIso.app ((sliceRestriction.{c, v, r} R W).obj N)).hom.val.app (op (Over.mk b))
    ((η.inv.app ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N)).val.app (op (Over.mk b)) y)

private def integralTensorNatIso :
    I.functor.prod I.functor ⋙
        @MonoidalCategory.tensor _ _ (monoidalCategory (R.over W)) ≅
      @MonoidalCategory.tensor _ _ (monoidalCategory S) ⋙
        I.functor := by
  let e := η
  exact Functor.isoWhiskerRight (NatIso.prod e e)
      (@MonoidalCategory.tensor _ _ (monoidalCategory (R.over W))) ≪≫
    tensorPushNatIso (F := F) (J := J.over W) (K := K)
      (hF := hF) (hFc := hFc) (ha := ha) (R.over W) S a ≪≫
      Functor.isoWhiskerLeft (@MonoidalCategory.tensor _ _
        (monoidalCategory S)) e.symm

private def transportedTensor
    (M N : scalarModules K S) :
    (SheafOfModules.monoidalCategory (R.over W)).tensorObj
        (I.functor.obj M) (I.functor.obj N) ≅
      I.functor.obj ((monoidalCategory S).tensorObj M N) := by
  let e := η
  exact @MonoidalCategory.tensorIso _ _
      (SheafOfModules.monoidalCategory (R.over W)) _ _ _ _ (e.app M) (e.app N) ≪≫
    tensorPush (F := F) (J := J.over W) (K := K)
      (hF := hF) (hFc := hFc) (ha := ha) (R.over W) S a M N ≪≫
      (e.app ((monoidalCategory S).tensorObj M N)).symm

private def localTensorTransport
    (M : scalarModules K S) (N : scalarModules J R) :
    (SheafOfModules.siteSheafTensorRight (A := R.over W)
      (N.over W)).obj (I.functor.obj M) ≅
      I.functor.obj
        ((monoidalCategory S).tensorObj M (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)) :=
  (tensorIsoSite (R.over W) _ _).symm ≪≫
    @MonoidalCategory.tensorIso _ _ (SheafOfModules.monoidalCategory (R.over W))
      _ _ _ _ (Iso.refl _) (I.counitIso.symm.app _) ≪≫
    transportedTensor.{c, v, r} R W S a I η M (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)

private def localTensorNatIso :
    I.functor.prod (sliceRestriction.{c, v, r} R W) ⋙ siteTensorFunctor (R.over W) ≅
      (𝟭 (scalarModules K S)).prod ((sliceRestriction.{c, v, r} R W ⋙ I.inverse)) ⋙
        @MonoidalCategory.tensor _ _ (monoidalCategory S) ⋙
          I.functor :=
  Functor.isoWhiskerLeft (I.functor.prod (sliceRestriction.{c, v, r} R W))
      (tensorToSite (R.over W)).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl I.functor)
        (Functor.isoWhiskerLeft (sliceRestriction.{c, v, r} R W) I.counitIso.symm))
      (@MonoidalCategory.tensor _ _ (monoidalCategory (R.over W))) ≪≫
    Functor.isoWhiskerLeft
      ((𝟭 (scalarModules K S)).prod ((sliceRestriction.{c, v, r} R W ⋙ I.inverse)))
      (integralTensorNatIso.{c, v, r} R W S a I η)

section

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

-- The four explicit tensor-section maps retain their full sheafification structures.
private theorem localTensorTransport_pure (M : scalarModules K S)
    (N : scalarModules J R) (V : C)
    (b : V ⟶ W)
    (x : M.val.obj (op (F.obj (Over.mk b))))
    (y : (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N).val.obj
      (op (F.obj (Over.mk b)))) :
    (localTensorTransport.{c, v, r} R W S a I η M N).hom.val.app (op (Over.mk b))
      (siteSheafTensorTmul (A := R.over W) (I.functor.obj M)
        (N.over W) (op (Over.mk b))
        ((η.inv.app M).val.app (op (Over.mk b)) x)
        (sliceRestrictedSection.{c, v, r} R W S a I η N V b y)) =
      ((η.inv.app
        ((monoidalCategory S).tensorObj M
          ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N))).val.app
          (op (Over.mk b)))
        (pure S M
          (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)
          (op (F.obj (Over.mk b))) x y) := by
  let e := η
  let q := I.counitIso.app ((sliceRestriction.{c, v, r} R W).obj N)
  let V₀ := op (Over.mk b)
  let ey := (e.app (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)).inv.val.app V₀ y
  have hq : q.inv.val.app V₀ (q.hom.val.app V₀ ey) = ey := by
    exact congrArg (fun f ↦ f.val.app V₀ ey) q.hom_inv_id
  have hx : (e.app M).hom.val.app V₀ ((e.app M).inv.val.app V₀ x) = x := by
    exact congrArg (fun f ↦ f.val.app V₀ x) (e.app M).inv_hom_id
  have hy : (e.app (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)).hom.val.app V₀ ey =
      y := by
    exact congrArg (fun f ↦ f.val.app V₀ y)
      (e.app (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)).inv_hom_id
  have ht := tensorIsoSite_inv_pure (R.over W)
    (I.functor.obj M) (N.over W) V₀
    ((e.app M).inv.val.app V₀ x) (q.hom.val.app V₀ ey)
  have h₁ := ScalarHomOrdinary.pure_map (R.over W)
    (𝟙 (I.functor.obj M)) q.inv V₀
    ((e.app M).inv.val.app V₀ x) (q.hom.val.app V₀ ey)
  have h₂ := ScalarHomOrdinary.pure_map (R.over W)
    (e.app M).hom (e.app (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N)).hom V₀
    ((e.app M).inv.val.app V₀ x) ey
  have hp := tensorPush_pure (F := F) (J := J.over W) (K := K)
      (hF := hF) (hFc := hFc) (ha := ha) (R.over W) S a
      M (((sliceRestriction.{c, v, r} R W ⋙ I.inverse)).obj N) V₀ x y
  change (e.app ((monoidalCategory S).tensorObj M
      ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N))).inv.val.app V₀
    ((tensorPush (F := F) (J := J.over W) (K := K)
      (hF := hF) (hFc := hFc) (ha := ha) (R.over W) S a M
      ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N)).hom.val.app V₀
        (((monoidalCategory (R.over W)).tensorHom (e.app M).hom
          (e.app ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N)).hom).val.app V₀
          (((monoidalCategory (R.over W)).tensorHom (𝟙 (I.functor.obj M)) q.inv).val.app V₀
            ((tensorIsoSite (R.over W) (I.functor.obj M) (N.over W)).inv.val.app V₀
              (siteSheafTensorTmul (I.functor.obj M) (N.over W) V₀
                ((e.app M).inv.val.app V₀ x) (q.hom.val.app V₀ ey)))))) = _
  erw [ht, h₁]
  change (e.app _).inv.val.app V₀
    ((tensorPush (F := F) (J := J.over W) (K := K)
      (hF := hF) (hFc := hFc) (ha := ha) (R.over W) S a
      M ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N)).hom.val.app V₀
        (((monoidalCategory (R.over W)).tensorHom (e.app M).hom
          (e.app ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N)).hom).val.app V₀
          (pure (R.over W) _ _ V₀ ((e.app M).inv.val.app V₀ x)
            (q.inv.val.app V₀ (q.hom.val.app V₀ ey))))) = _
  rw [hq, h₂, hx, hy, hp]
  rfl

end

-- The composed two-variable isomorphism and its section equation have large dependent types.
/-- Transport of the normalized slice tensor formula through a coefficient equivalence.
Source: Stacks 03DI, 03EK and 0E8I
(blueprint: lem-sf-open-ringed-coefficient-tensor-transport).

Proof: the coefficient tensorator is induced by the identity on presheaf pure
sections and sheafification. Insert the inverse module-equivalence counit in the
second factor and compose with the tensorator. Apply localized extension to this
natural isomorphism and compose with the normalized slice projection formula.
On each original extension summand the slice formula gives the corresponding
slice pure tensor. The inverse counit cancels the counit in the restricted
section, the coefficient tensorator preserves the two original sections, and
extension of a map acts in that same summand. Naturality follows by composition
of the three natural isomorphisms. -/
theorem ringedCoefficientTensorTransport :
    let L := I.functor ⋙ localizedSystemExtension.{c, v, r} R W
    let P := localizedSystemRestriction.{c, v, r} R W ⋙ I.inverse
    ∃ μ : ∀ (M : scalarModules K S) (N : scalarModules J R),
        (monoidalCategory R).tensorObj (L.obj M) N ≅
          L.obj ((monoidalCategory S).tensorObj M (P.obj N)),
      (∀ {M M' : scalarModules K S} {N N' : scalarModules J R}
        (f : M ⟶ M') (g : N ⟶ N'),
        (monoidalCategory R).tensorHom (L.map f) g ≫ (μ M' N').hom =
          (μ M N).hom ≫ L.map ((monoidalCategory S).tensorHom f (P.map g))) ∧
      ∀ (M : scalarModules K S) (N : scalarModules J R) (V : C) (b : V ⟶ W)
        (x : M.val.obj (op (F.obj (Over.mk b))))
        (y : (P.obj N).val.obj (op (F.obj (Over.mk b)))),
        (μ M N).hom.val.app (op V)
          (pure R (L.obj M) N (op V)
            (ringedSliceExtensionSection.{c, v, r} R W (I.functor.obj M) (Over.mk b)
              ((η.inv.app M).val.app (op (Over.mk b)) x))
            ((I.counitIso.app (N.over W)).hom.val.app (op (Over.mk b))
              ((η.inv.app (P.obj N)).val.app (op (Over.mk b)) y))) =
          ringedSliceExtensionSection.{c, v, r} R W
            (I.functor.obj ((monoidalCategory S).tensorObj M (P.obj N))) (Over.mk b)
            ((η.inv.app ((monoidalCategory S).tensorObj M (P.obj N))).val.app
              (op (Over.mk b)) (pure S M (P.obj N) (op (F.obj (Over.mk b))) x y)) := by
  obtain ⟨e, he, _, hn, _⟩ := exists_ringedSliceTensorGenerators.{c, v, r} R W
  let p :
      (I.functor ⋙ sliceExtension.{c, v, r} R W).prod (𝟭 (scalarModules J R)) ⋙
          siteTensorFunctor R ≅
        I.functor.prod (sliceRestriction.{c, v, r} R W) ⋙
          siteTensorFunctor (R.over W) ⋙ sliceExtension.{c, v, r} R W :=
    NatIso.ofComponents (fun MN ↦ e (I.functor.obj MN.1) MN.2) (by
      intro MN MN' f
      have h₁ := siteTensorFunctor_map R ((I.functor ⋙ sliceExtension.{c, v, r} R W).map f.1) f.2
      have h₂ := siteTensorFunctor_map (R.over W) (I.functor.map f.1)
        ((sliceRestriction.{c, v, r} R W).map f.2)
      exact (congrArg (fun k ↦ k ≫ (e (I.functor.obj MN'.1) MN'.2).hom) h₁).trans
        ((hn _ _ _ _ (I.functor.map f.1) f.2).trans
          (congrArg (fun k ↦ (e (I.functor.obj MN.1) MN.2).hom ≫
            (sliceExtension.{c, v, r} R W).map k) h₂).symm))
  let μNat :
      (I.functor ⋙ sliceExtension.{c, v, r} R W).prod (𝟭 (scalarModules J R)) ⋙
          @MonoidalCategory.tensor _ _ (monoidalCategory R) ≅
        (𝟭 (scalarModules K S)).prod (sliceRestriction.{c, v, r} R W ⋙ I.inverse) ⋙
          @MonoidalCategory.tensor _ _ (monoidalCategory S) ⋙
            I.functor ⋙ sliceExtension.{c, v, r} R W :=
    Functor.isoWhiskerLeft ((I.functor ⋙ sliceExtension.{c, v, r} R W).prod (𝟭 (scalarModules J R)))
      (tensorToSite R) ≪≫ p ≪≫
        Functor.isoWhiskerRight (localTensorNatIso.{c, v, r} R W S a I η)
          (sliceExtension.{c, v, r} R W)
  refine ⟨fun M N ↦ μNat.app (M, N), ?_, ?_⟩
  · intro M M' N N' f g
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map,
      CategoryTheory.Functor.id_map, MonoidalCategory.tensor_map, Iso.app_hom] using
        μNat.hom.naturality (Prod.mkHom f g)
  · intro M N V b x y
    change ((sliceExtension.{c, v, r} R W).map
        (localTensorTransport.{c, v, r} R W S a I η M N).hom).val.app (op V)
      ((e (I.functor.obj M) N).hom.val.app (op V)
        ((tensorIsoSite R _ N).hom.val.app (op V)
          (pure R _ N (op V)
            (ringedSliceExtensionSection.{c, v, r} R W (I.functor.obj M) (Over.mk b)
              ((η.inv.app M).val.app (op (Over.mk b)) x))
            (sliceRestrictedSection.{c, v, r} R W S a I η N V b y)))) = _
    let tt := localTensorTransport.{c, v, r} R W S a I η M N
    let x₀ := (η.inv.app M).val.app (op (Over.mk b)) x
    let y₀ := sliceRestrictedSection.{c, v, r} R W S a I η N V b y
    let z := siteSheafTensorTmul (I.functor.obj M) (N.over W) (op (Over.mk b)) x₀ y₀
    have h₀ := tensorIsoSite_pure R ((I.functor ⋙ sliceExtension.{c, v, r} R W).obj M)
      N (op V) (ringedSliceExtensionSection.{c, v, r} R W (I.functor.obj M)
        (Over.mk b) x₀) y₀
    have h₁ := he (I.functor.obj M) N (Over.mk b) x₀ y₀
    have h₂ := SheafOfModules.extension_map.{c, v, r} R W tt.hom (Over.mk b) z
    have h₃ := localTensorTransport_pure.{c, v, r} R W S a I η M N V b x y
    exact (congrArg (fun u ↦ ((sliceExtension.{c, v, r} R W).map tt.hom).val.app (op V)
        ((e (I.functor.obj M) N).hom.val.app (op V) u)) h₀).trans
      ((congrArg (((sliceExtension.{c, v, r} R W).map tt.hom).val.app (op V)) h₁).trans
        (h₂.trans (congrArg (fun u ↦ ringedSliceExtensionSection.{c, v, r} R W
          (I.functor.obj ((monoidalCategory S).tensorObj M
            ((sliceRestriction.{c, v, r} R W ⋙ I.inverse).obj N))) (Over.mk b) u) h₃)))

end WeilConjectures.OpenSemilinearTensor
