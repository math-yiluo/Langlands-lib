/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalProEtaleRealization
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
/-! # Realization of the actual etale/pro-etale system comparison
Source: blueprint theorem-f-shriek-finite-coefficients. All ordinary maps are fixed on
sections or by adjunction transposes; their derived maps retain the localization units.
(blueprint: def-pur-adic-site-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
private theorem constantSection_apply
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (a : A) (U : Cᵒᵖ)
    (z : ((constantSheaf J (Type (u + 1))).obj PUnit).obj.obj U) :
    ((((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).symm
      ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))).hom.app U z) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  let T := (Functor.const Cᵒᵖ).obj (PUnit.{u + 2} : Type (u + 1))
  have hT : Presheaf.IsSheaf J T := Sheaf.tensorUnit_isSheaf J
  have : IsIso (toSheafify J T) := isIso_toSheafify J hT
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J T).app U)).surjective z
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).apply_symm_apply
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (CategoryTheory.forget CommRingCat.{u + 1}))
  exact congrArg (fun f ↦ f.app U t) h

private theorem constantRingScalar
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of A)).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso Cᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
            (CommRingCat.of A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a)) = _
  have hi : ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of A)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app U a) h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E))
  (B : IntegralExceptionalComparison l E W P)

private theorem integralExceptionalSiteRight_underlying_apply (n : ℕ)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
    (T : Sheaf W.smallEtaleTopology (Type (u + 1)))
    (a : T ⟶ (coefficientUnderlying (J := W.smallEtaleTopology)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj
        ((B.ordinary.right n).obj M)) (U : W.Etaleᵒᵖ) (z : T.obj.obj U) :
    ((B.ordinary.rightUnderlying n).hom.app M).hom.app U (a.hom.app U z) =
    ((B.ordinary.levelAdj n).counit.app M).val.app ((Scheme.toProEt W).op.obj U)
      (((B.ordinary.lift n).moduleUnderlying.inv.app
        ((B.ordinary.right n).obj M)).hom.app ((Scheme.toProEt W).op.obj U)
        (((integralExceptionalSetInverse W).map a).hom.app ((Scheme.toProEt W).op.obj U)
          (((Scheme.proEtaleSiteComparison W).unit.app T).hom.app U z))) := by
  let L := integralExceptionalSetInverse W
  let adj := Scheme.proEtaleSiteComparison W
  let Q := coefficientUnderlying (J := W.smallEtaleTopology)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let V := coefficientUnderlying (J := Scheme.ProEt.topology W)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let I := B.ordinary.lift n
  let R := B.ordinary.right n
  let β := B.ordinary.rightUnderlying n
  have hβ (M) : β.hom.app M = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app (R.obj M) ≫
        V.map ((B.ordinary.levelAdj n).counit.app M)) := by
    have hc : (B.ordinary.levelAdj n).homEquiv (R.obj M) M
        ((B.ordinary.levelAdj n).counit.app M) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact ((B.ordinary.levelAdj n).homEquiv (R.obj M) M).apply_symm_apply _
    have h := B.ordinary.levelTranspose n (R.obj M) M
      ((B.ordinary.levelAdj n).counit.app M)
    change (B.ordinary.levelAdj n).homEquiv (R.obj M) M
      ((B.ordinary.levelAdj n).counit.app M) = 𝟙 _ at hc
    change Q.map ((B.ordinary.levelAdj n).homEquiv (R.obj M) M
      ((B.ordinary.levelAdj n).counit.app M)) ≫ β.hom.app M = _ at h
    rw [hc, Q.map_id, Category.id_comp] at h
    exact h
  have hβ' := (hβ M).trans (adj.homEquiv_unit _ _ _)
  refine (congrArg (fun f ↦ f.hom.app U (a.hom.app U z)) hβ').trans ?_
  have h := congrArg (fun f ↦ f.hom.app U z) (adj.unit.naturality a)
  change (adj.unit.app (Q.obj (R.obj M))).hom.app U (a.hom.app U z) =
    (L.map a).hom.app ((Scheme.toProEt W).op.obj U)
      ((adj.unit.app T).hom.app U z) at h
  exact congrArg (fun x ↦
    ((B.ordinary.levelAdj n).counit.app M).val.app ((Scheme.toProEt W).op.obj U)
      ((I.moduleUnderlying.inv.app (R.obj M)).hom.app
        ((Scheme.toProEt W).op.obj U) x)) h

private theorem integralExceptionalSiteRight_map_add (n : ℕ)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
    (U : W.Etaleᵒᵖ) (x y : ((B.ordinary.right n).obj M).val.obj U) :
    ((B.ordinary.rightUnderlying n).hom.app M).hom.app U (x + y) =
      (show M.val.obj ((Scheme.toProEt W).op.obj U) from
        ((B.ordinary.rightUnderlying n).hom.app M).hom.app U x) +
      (show M.val.obj ((Scheme.toProEt W).op.obj U) from
        ((B.ordinary.rightUnderlying n).hom.app M).hom.app U y) := by
  let adj := Scheme.proEtaleSiteComparison W
  let Q := coefficientUnderlying (J := W.smallEtaleTopology)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let I := B.ordinary.lift n
  let R := B.ordinary.right n
  let β := B.ordinary.rightUnderlying n
  have hunit := integralExceptionalSiteRight_underlying_apply l E W P B n
  let X := Q.obj (R.obj M)
  let T := (CategoryTheory.MonoidalCategory.tensorObj X X)
  let a : T ⟶ X := CartesianMonoidalCategory.fst X X
  let b : T ⟶ X := CartesianMonoidalCategory.snd X X
  let t : T ⟶ X := ⟨{
    app := fun Y ↦ ↾fun z ↦
      (show (R.obj M).val.obj Y from z.1) +
        (show (R.obj M).val.obj Y from z.2)
    naturality := by
      intro Y Z f
      ext z
      exact ((R.obj M).val.map f).hom.map_add z.1 z.2 |>.symm }⟩
  have h := I.moduleAdd (R.obj M) T a b t (fun _ _ ↦ rfl)
    ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U (x, y))
  have ha := hunit M T a U (x, y)
  have hb := hunit M T b U (x, y)
  have ht := hunit M T t U (x, y)
  change (β.hom.app M).hom.app U (x + y) = _ at ht
  change (β.hom.app M).hom.app U x = _ at ha
  change (β.hom.app M).hom.app U y = _ at hb
  dsimp only [id] at h
  let ε := (((B.ordinary.levelAdj n).counit.app M).val.app
    ((Scheme.toProEt W).op.obj U)).hom
  exact ht.trans ((congrArg ε h).trans
    ((ε.map_add _ _).trans (congrArg₂ (· + ·) ha.symm hb.symm)))

private theorem integralExceptionalSiteRight_map_smul (n : ℕ)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
    (U : W.Etaleᵒᵖ) (q : integralExceptionalQuotientRing l E n)
    (x : ((B.ordinary.right n).obj M).val.obj U) :
    ((B.ordinary.rightUnderlying n).hom.app M).hom.app U
      ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app U q • x) =
    (toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
      (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app
        ((Scheme.toProEt W).op.obj U) q •
      (show M.val.obj ((Scheme.toProEt W).op.obj U) from
        ((B.ordinary.rightUnderlying n).hom.app M).hom.app U x) := by
  let L := integralExceptionalSetInverse W
  let adj := Scheme.proEtaleSiteComparison W
  let Q := coefficientUnderlying (J := W.smallEtaleTopology)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let I := B.ordinary.lift n
  let R := B.ordinary.right n
  let β := B.ordinary.rightUnderlying n
  have hunit := integralExceptionalSiteRight_underlying_apply l E W P B n
  let X := Q.obj (R.obj M)
  let S := (constantSheaf W.smallEtaleTopology (Type (u + 1))).obj PUnit
  let T := CategoryTheory.MonoidalCategory.tensorObj S X
  let a : T ⟶ _ := CartesianMonoidalCategory.fst S X ≫
    coefficientConstantSection (J := W.smallEtaleTopology)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n q
  let b : T ⟶ X := CartesianMonoidalCategory.snd S X
  let t : T ⟶ X := ⟨{
    app := fun Y ↦ ↾fun z ↦
      (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj Y
          from a.hom.app Y z) • (show (R.obj M).val.obj Y from z.2)
    naturality := by
      intro Y Z f
      ext z
      have hn := congrArg (fun k ↦ k z) (a.hom.naturality f).symm
      change (coefficientQuotientSheaf (J := W.smallEtaleTopology)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.map f
          (a.hom.app Y z) = a.hom.app Z (T.obj.map f z) at hn
      symm
      change (R.obj M).val.map f
        ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj Y
            from a.hom.app Y z) • (show (R.obj M).val.obj Y from z.2)) =
        (show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj Z
            from a.hom.app Z (T.obj.map f z)) •
          (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)
      exact ((R.obj M).val.map_smul f _ _).trans (congrArg (fun c : (coefficientQuotientSheaf
        (J := W.smallEtaleTopology) (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n).obj.obj Z ↦
          c • (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)) hn) }⟩
  let z : T.obj.obj U :=
    ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
      (PUnit.{u + 2} : Type (u + 1)))).app U PUnit.unit, x)
  have ha : a.hom.app U z =
      (toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app U q :=
    constantSection_apply W.smallEtaleTopology _ q U z.1
  have h := I.moduleSMul (R.obj M) T a b t (fun _ _ ↦ rfl)
    ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U z)
  have hc : L.map a ≫ I.ringUnderlying.hom =
      L.map (CartesianMonoidalCategory.fst S X) ≫ B.ordinary.singleton.hom ≫
        coefficientConstantSection (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n q := by
    dsimp only [a]
    rw [L.map_comp, Category.assoc, B.ordinary.constants]
  have hc' := congrArg (fun f ↦ f.hom.app ((Scheme.toProEt W).op.obj U)
    ((adj.unit.app T).hom.app U z)) hc
  have ht := hunit M T t U z
  have hb := hunit M T b U z
  change (β.hom.app M).hom.app U
    ((show (coefficientQuotientSheaf (J := W.smallEtaleTopology)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj U
        from a.hom.app U z) • x) = _ at ht
  change (β.hom.app M).hom.app U x = _ at hb
  have ht' := (congrArg (fun c : (coefficientQuotientSheaf
    (J := W.smallEtaleTopology) (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n).obj.obj U ↦
        (β.hom.app M).hom.app U (c • x)) ha).symm.trans ht
  dsimp only [id] at h
  have hconst := constantSection_apply (Scheme.ProEt.topology W)
    (integralExceptionalQuotientRing l E n) q ((Scheme.toProEt W).op.obj U)
    ((B.ordinary.singleton.hom).hom.app ((Scheme.toProEt W).op.obj U)
      ((L.map (CartesianMonoidalCategory.fst S X)).hom.app
        ((Scheme.toProEt W).op.obj U) ((adj.unit.app T).hom.app U z)))
  change (I.ringUnderlying.hom).hom.app ((Scheme.toProEt W).op.obj U)
    ((L.map a).hom.app ((Scheme.toProEt W).op.obj U)
      ((adj.unit.app T).hom.app U z)) = _ at hc'
  have hs := hc'.trans hconst
  let ε := (((B.ordinary.levelAdj n).counit.app M).val.app
    ((Scheme.toProEt W).op.obj U)).hom
  exact ht'.trans ((congrArg ε h).trans
    ((ε.map_smul _ _).trans (congrArg₂ (· • ·) hs hb.symm)))

/-- Ordinary site direct-image realization, fixed on every section by the actual
underlying set-sheaf comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization).
Proof: both direct images restrict a sheaf along the actual etale-to-pro-etale functor. The
recorded rightUnderlying map identifies their values on each etale test object. The
quotient coordinate equivalence fixes constants, so these maps are linear, natural,
and invertible. Faithful forgetting to set sheaves proves uniqueness. -/
theorem integralExceptionalSiteRight_existsUnique (n : ℕ) :
    ∃! e : B.ordinary.right n ⋙ integralExceptionalEtaleRealization l E W n ≅
      integralExceptionalProRealization l E W n ⋙
        ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W,
      ∀ (M : coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
        (U : W.Etaleᵒᵖ) (x : ((B.ordinary.right n).obj M).val.obj U),
        (e.hom.app M).hom.app U x =
          ((B.ordinary.rightUnderlying n).hom.app M).hom.app U x := by
  let := integralExceptionalEtaleForget W
  let := Scheme.purTwistForgetPreservesSheafification W
  let R := B.ordinary.right n
  let β := B.ordinary.rightUnderlying n
  have hadd := integralExceptionalSiteRight_map_add l E W P B n
  have hsmul := integralExceptionalSiteRight_map_smul l E W P B n
  let F := R ⋙ integralExceptionalEtaleRealization l E W n
  let G := integralExceptionalProRealization l E W n ⋙
    ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W
  let γ : F ⟶ G := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).obj.obj U) (Y := (G.obj M).obj.obj U) {
        toFun := fun x ↦ (β.hom.app M).hom.app U x
        map_add' := fun x y ↦ hadd M U x y
        map_smul' := by
          intro c x
          change (β.hom.app M).hom.app U
            (((constantCommuteCompose W.smallEtaleTopology
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                (CommRingCat.of (integralExceptionalQuotientRing l E n))).hom.app U
                  ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
                    (RingCat.of (integralExceptionalQuotientRing l E n)))).app U
                      ((integralExceptionalQuotient l E n).symm c)) •
                (show (R.obj M).val.obj U from x)) =
            (((constantCommuteCompose (Scheme.ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                (CommRingCat.of (integralExceptionalQuotientRing l E n))).hom.app
                  ((Scheme.toProEt W).op.obj U)
                    ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
                      (RingCat.of (integralExceptionalQuotientRing l E n)))).app
                        ((Scheme.toProEt W).op.obj U)
                          ((integralExceptionalQuotient l E n).symm c))) •
              (show M.val.obj ((Scheme.toProEt W).op.obj U) from
                (β.hom.app M).hom.app U x)
          rw [constantRingScalar, constantRingScalar]
          exact hsmul M U ((integralExceptionalQuotient l E n).symm c) x }
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun k ↦ k x) ((β.hom.app M).hom.naturality f) } }
    naturality := by
      intro M N f
      ext U x
      exact congrArg (fun k ↦ k.hom.app U x) (β.hom.naturality f) }
  have hγ (M) : IsIso (γ.app M) := by
    have hpoint (U) : IsIso ((γ.app M).hom.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso ((β.hom.app M).hom.app U)
    have : IsIso ((sheafToPresheaf W.smallEtaleTopology _).map (γ.app M)) :=
      NatIso.isIso_of_isIso_app (γ.app M).hom
    exact isIso_of_reflects_iso (γ.app M) (sheafToPresheaf W.smallEtaleTopology _)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  refine ⟨asIso γ, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    apply funext
    intro M
    ext U x
    exact he M U x

/-- The ordinary direct realization, fixed on all sections.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization). -/
def integralExceptionalSiteRight (n : ℕ) :=
  (integralExceptionalSiteRight_existsUnique l E W P B n).exists.choose

/-- Ordinary inverse realization, fixed by its full adjunction transpose equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization).
Proof: transport the two site adjunctions along the exact realization equivalences.Take
 the mate of the already section-normalized ordinary direct comparison. The
adjunction bijections imply the displayed equation and uniqueness of the map. -/
theorem integralExceptionalSiteInverse_existsUnique (n : ℕ) :
    ∃! e : (B.ordinary.lift n).modules ⋙ integralExceptionalProRealization l E W n ≅
      integralExceptionalEtaleRealization l E W n ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W,
      ∀ (M : strictEtaleLevel W (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : coefficientLevelModules (J := Scheme.ProEt.topology W)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n)
        (h : (B.ordinary.lift n).modules.obj M ⟶ N),
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalProRealization l E W n).map h) =
        (integralExceptionalEtaleRealization l E W n).map
          ((B.ordinary.levelAdj n).homEquiv _ _ h) ≫
            (integralExceptionalSiteRight l E W P B n).hom.app N := by
  let adj₁ := B.ordinary.levelAdj n
  let adj₂ := ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W
  let β := integralExceptionalSiteRight l E W P B n
  let α := ((mateEquiv adj₁ adj₂).symm β.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences adj₁ adj₂ β
  let e := (asIso α).symm
  have he M N (h : (B.ordinary.lift n).modules.obj M ⟶ N) :
      adj₂.homEquiv _ _ (e.inv.app M ≫
        (integralExceptionalProRealization l E W n).map h) =
      (integralExceptionalEtaleRealization l E W n).map (adj₁.homEquiv _ _ h) ≫
        β.hom.app N := by
    rw [adj₂.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    have hu := unit_mateEquiv_symm adj₁ adj₂ β.hom M
    change (integralExceptionalEtaleRealization l E W n).map (adj₁.unit.app M) ≫
      β.hom.app ((B.ordinary.lift n).modules.obj M) =
      adj₂.unit.app _ ≫ _ at hu
    change (integralExceptionalEtaleRealization l E W n).map (adj₁.unit.app M) ≫
      β.hom.app ((B.ordinary.lift n).modules.obj M) =
      adj₂.unit.app _ ≫ (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).map
          (e.inv.app M) at hu
    rw [← hu]
    have hn := β.hom.naturality h
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn]
    simp only [← Category.assoc, ← Functor.map_comp,
      Adjunction.homEquiv_unit]
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hi : e'.inv = e.inv := by
    apply NatTrans.ext
    apply funext
    intro M
    apply (adj₂.homEquiv _ _).injective
    have h := (he' M _ (𝟙 _)).trans (he M _ (𝟙 _)).symm
    change adj₂.homEquiv _ _ (e'.inv.app M ≫
      (integralExceptionalProRealization l E W n).map (𝟙 _)) =
      adj₂.homEquiv _ _ (e.inv.app M ≫
        (integralExceptionalProRealization l E W n).map (𝟙 _)) at h
    simp only [CategoryTheory.Functor.map_id] at h
    exact h
  exact Iso.ext_inv hi

/-- The specified ordinary inverse comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-site-realization). -/
@[no_expose] def integralExceptionalSiteInverse (n : ℕ) :=
  (integralExceptionalSiteInverse_existsUnique l E W P B n).exists.choose

end WeilConjectures
