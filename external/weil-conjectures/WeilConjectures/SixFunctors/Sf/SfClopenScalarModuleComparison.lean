/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import all WeilConjectures.SixFunctors.Sf.SfClopenScalarRawRestrictionComparison
import all WeilConjectures.Algebra.Homology.QuotientIsoTransport.RingIsoQuotientSystemTransport
/-! # Ordinary scalar extension comparison on a clopen component
Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-sf-clopen-scalar-module-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open SheafOfModules SheafOfModules.StrictScalarHom
open ProEt.ClopenScalar ProEt.ClopenData
open SheafOfModules.QuotientIsoTransport
open scoped ChangeOfRings
attribute [local instance 20000] SheafOfModules.systemRingHasDerived
  SheafOfModules.instAbelian

private instance (priority := 20000) sfScalarSiteSmall (Z : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} Z.ProEt := essentiallySmallSelf _

private instance (priority := 20000) sfScalarAbSheafify (Z : Scheme.{t}) :
    HasSheafify (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} Z
private instance (priority := 20000) sfScalarAbLocallyBijective (Z : Scheme.{t}) :
    (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} Z

private def sfScalarModelIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (n : ℕ)
    (A : SystemScalarModel.{t + 1, t, max u (t + 1)} (J := ProEt.topology T)
      (completedIntegralCommRingProjectionUnrestricted l E T n)) :
    A.model.E ≅ scalarReductionExtension l E T n := by
  let hobj : ∀ M : scalarReductionSource l E T,
      (scalarReductionExtension l E T n).obj M =
        changeOfRings (completedIntegralCommRingProjectionUnrestricted l E T n) M :=
    (scalarReductionExistence l E T n).choose_spec.choose
  let hmap := @(scalarReductionExistence l E T n).choose_spec.choose_spec.choose
  refine NatIso.ofComponents
    (fun M ↦ eqToIso (A.model.obj_eq M) ≪≫ eqToIso (hobj M).symm) ?_
  intro M N f
  dsimp only [Iso.trans_hom, eqToIso.hom]
  dsimp only [scalarReductionExtension]
  rw [A.model.map_eq, hmap]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private theorem sfScalarModelIso_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (n : ℕ)
    (A : SystemScalarModel.{t + 1, t, max u (t + 1)} (J := ProEt.topology T)
      (completedIntegralCommRingProjectionUnrestricted l E T n))
    (M : scalarReductionSource l E T) (V : T.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E T n).obj.obj V) (x : M.val.obj V) :
    ((sfScalarModelIso l E T n A).hom.app M).val.app V
      (systemModelTmul A.model M V s x) =
        unrestrictedTowerTensorSection l E T n M V s x := by
  rw [sfSystemTensor_eq.{t, u}]
  unfold sfScalarModelIso
  dsimp only [NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom]
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

private theorem sfLiftedProjectionSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :
    let rings := clopenTensorRings.{t, u} U.ι
    let ff := fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
      CommRingCat.fullyFaithfulForget₂ToRingCat
    (ff.preimageIso
      (X := completedIntegralCommRingSheafUnrestricted l E U.toScheme)
      (Y := rings.obj (completedIntegralCommRingSheafUnrestricted l E T)) d.completion).hom ≫
        rings.map (completedIntegralCommRingProjectionUnrestricted l E T n) =
      completedIntegralCommRingProjectionUnrestricted l E U.toScheme n ≫
        (ff.preimageIso
          (X := integralCoefficientCommRingSheaf l E U.toScheme n)
          (Y := rings.obj (integralCoefficientCommRingSheaf l E T n)) (d.finite n)).hom := by
  let rings := clopenTensorRings.{t, u} U.ι
  let ff := fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
    CommRingCat.fullyFaithfulForget₂ToRingCat
  let co : completedIntegralCommRingSheafUnrestricted l E U.toScheme ≅
      rings.obj (completedIntegralCommRingSheafUnrestricted l E T) :=
    ff.preimageIso d.completion
  let cs : integralCoefficientCommRingSheaf l E U.toScheme n ≅
      rings.obj (integralCoefficientCommRingSheaf l E T n) :=
    ff.preimageIso (d.finite n)
  change co.hom ≫ rings.map (completedIntegralCommRingProjectionUnrestricted l E T n) =
    completedIntegralCommRingProjectionUnrestricted l E U.toScheme n ≫ cs.hom
  apply (sheafCompose (ProEt.topology U.toScheme)
    (forget₂ CommRingCat RingCat)).map_injective
  have hco : (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat RingCat)).map co.hom = d.completion.hom := ff.map_preimage _
  have hcs : (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat RingCat)).map cs.hom = (d.finite n).hom := ff.map_preimage _
  simp only [Functor.map_comp, hco, hcs]
  change d.completion.hom ≫
      ((sfClopenSiteInclusion U).sheafPushforwardContinuous RingCat
        (ProEt.topology U.toScheme) (ProEt.topology T)).map
          (limit.π (integralCoefficientSheafSystem l E T) (op n)) =
    limit.π (integralCoefficientSheafSystem l E U.toScheme) (op n) ≫ (d.finite n).hom
  exact d.projection n

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExtension unrestrictedTowerTensorSection

attribute [local irreducible] sfScalarModelIso ordinaryScalarSquare

/-- Restriction commutes with ordinary scalar extension, with its normalized tensor formula.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 03CY;
sites-cohomology.tex, Tag 06YY.
(blueprint: lem-sf-clopen-scalar-module-comparison).

Proof: first use cocontinuity of the open-site inclusion to compare the sheafifications
of the restricted tensor presheaf. Transport this comparison through the object and map
equations of the recorded ordinary scalar models. Lift the coefficient comparisons to
commutative-ring sheaf isomorphisms; their square is `d.projection`. The normalized
scalar square for these ring isomorphisms identifies the restricted scalar model with
the local scalar model. Transport the latter to the specified scalar-reduction functor
by its object and map equations. On pure tensors the first comparison preserves the
coefficient, the scalar square applies the inverse finite coefficient isomorphism, and
the final transport preserves the sheafification unit. The inverse finite coefficient
map cancels `d.finite(s)`, giving the displayed formula. Every construction is natural
in the module and also applies to an empty component and zero rings. -/
theorem sf_clopen_scalar_module_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :
    ∃ c : scalarReductionExtension l E T n ⋙
        sfClopenModuleRestriction U _ _ (d.finite n) ≅
      sfClopenModuleRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
        (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion ⋙
        scalarReductionExtension l E U.toScheme n,
      ∀ (M : scalarReductionSource l E T) (V : U.toScheme.ProEt)
        (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
        (x : M.val.obj (op ((sfClopenSiteInclusion U).obj V))),
      ((c.hom.app M).val.app (op V))
        (unrestrictedTowerTensorSection l E T n M
          (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
      unrestrictedTowerTensorSection l E U.toScheme n
        ((sfClopenModuleRestriction U _ _ d.completion).obj M) (op V) s x := by
  classical
  let rings := clopenTensorRings.{t, u} U.ι
  let a := completedIntegralCommRingProjectionUnrestricted l E T n
  let b := completedIntegralCommRingProjectionUnrestricted l E U.toScheme n
  let ff := fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
    CommRingCat.fullyFaithfulForget₂ToRingCat
  let co : completedIntegralCommRingSheafUnrestricted l E U.toScheme ≅
      rings.obj (completedIntegralCommRingSheafUnrestricted l E T) :=
    ff.preimageIso d.completion
  let cs : integralCoefficientCommRingSheaf l E U.toScheme n ≅
      rings.obj (integralCoefficientCommRingSheaf l E T n) :=
    ff.preimageIso (d.finite n)
  have hco : (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat RingCat)).map co.hom = d.completion.hom := ff.map_preimage _
  have hcs : (sheafCompose (ProEt.topology U.toScheme)
      (forget₂ CommRingCat RingCat)).map cs.hom = (d.finite n).hom := ff.map_preimage _
  have hp : co.hom ≫ rings.map a = b ≫ cs.hom :=
    sfLiftedProjectionSquare l E T U d n
  have h : co.inv ≫ b = rings.map a ≫ cs.inv := by
    apply (cancel_epi co.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : EssentiallySmall.{max u (t + 1)} U.toScheme.ProEt := essentiallySmallSelf _
  obtain ⟨A⟩ := nonempty_systemScalarModel.{t + 1, t, max u (t + 1)}
    (J := ProEt.topology U.toScheme) (rings.map a)
  obtain ⟨B⟩ := nonempty_systemScalarModel.{t + 1, t, max u (t + 1)}
    (J := ProEt.topology U.toScheme) b
  let L := clopenTensorRestriction.{t, u} U.ι
    (completedIntegralCommRingSheafUnrestricted l E T)
  obtain ⟨back, hbackTensor⟩ := sf_clopen_scalar_raw_restriction_comparison l E T U n A
  let β := ordinaryScalarSquare (rings.map a) b co.symm cs.symm h A B
  let N := clopenTensorRestriction.{t, u} U.ι (integralCoefficientCommRingSheaf l E T n)
  let completedTransport := transport.{t + 1, t, max u (t + 1)}
    (J := ProEt.topology U.toScheme) co.symm
  let finiteTransport := transport.{t + 1, t, max u (t + 1)}
    (J := ProEt.topology U.toScheme) cs.symm
  let c := (Functor.associator (scalarReductionExtension l E T n) N
      finiteTransport).symm ≪≫
    Functor.isoWhiskerRight back.symm finiteTransport ≪≫
      Functor.associator L A.model.E finiteTransport ≪≫
    Functor.isoWhiskerLeft L β ≪≫
      (Functor.associator L completedTransport B.model.E).symm ≪≫
      Functor.isoWhiskerLeft (L ⋙ completedTransport) (sfScalarModelIso l E U.toScheme n B) ≪≫
      Functor.associator L completedTransport (scalarReductionExtension l E U.toScheme n)
  have result : ∃ c : scalarReductionExtension l E T n ⋙
        clopenTensorRestriction.{t, u} U.ι (integralCoefficientCommRingSheaf l E T n) ⋙
          finiteTransport ≅
      L ⋙ completedTransport ⋙ scalarReductionExtension l E U.toScheme n,
      ∀ (M : scalarReductionSource l E T) (V : U.toScheme.ProEt)
        (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
        (x : M.val.obj (op ((sfClopenSiteInclusion U).obj V))),
      ((c.hom.app M).val.app (op V))
        (unrestrictedTowerTensorSection l E T n M
          (op ((sfClopenSiteInclusion U).obj V)) (cs.hom.hom.app (op V) s) x) =
      unrestrictedTowerTensorSection l E U.toScheme n
        ((L ⋙ completedTransport).obj M) (op V) s x := by
    refine ⟨c, ?_⟩
    intro M V s x
    have hb := hbackTensor M (op V)
      (cs.hom.hom.app (op V) s) x
    have hh := congrArg (fun z ↦ (back.inv.app M).val.app (op V) z) hb
    have hi := congrArg (fun f ↦ f.val.app (op V)
      (systemModelTmul A.model (L.obj M) (op V) (cs.hom.hom.app (op V) s) x))
        (back.hom_inv_id_app M)
    have hback : (back.inv.app M).val.app (op V)
        (unrestrictedTowerTensorSection l E T n M
          (op ((sfClopenSiteInclusion U).obj V)) (cs.hom.hom.app (op V) s) x) =
      systemModelTmul A.model (L.obj M) (op V) (cs.hom.hom.app (op V) s) x :=
      hh.symm.trans hi
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.comp_id]
    change ((sfScalarModelIso l E U.toScheme n B).hom.app
        ((L ⋙ completedTransport).obj M)).val.app (op V)
      ((β.hom.app (L.obj M)).val.app (op V)
        ((back.inv.app M).val.app (op V)
          (unrestrictedTowerTensorSection l E T n M
            (op ((sfClopenSiteInclusion U).obj V)) (cs.hom.hom.app (op V) s) x))) = _
    rw [hback]
    have hβ := ordinaryScalarSquare_tmul (rings.map a) b co.symm cs.symm h A B
      (L.obj M) (op V) x (cs.hom.hom.app (op V) s)
    change (β.hom.app (L.obj M)).val.app (op V)
      (systemModelTmul A.model (L.obj M) (op V) (cs.hom.hom.app (op V) s) x) =
      systemModelTmul B.model ((L ⋙ completedTransport).obj M) (op V)
        (cs.inv.hom.app (op V) (cs.hom.hom.app (op V) s)) x at hβ
    rw [hβ]
    have hs := congrArg (fun f ↦ f.hom.app (op V) s) cs.hom_inv_id
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, CommRingCat.comp_apply,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, CommRingCat.id_apply] at hs
    rw [hs]
    exact sfScalarModelIso_tensor l E U.toScheme n B
      ((L ⋙ completedTransport).obj M) (op V) s x
  dsimp +instances only [completedTransport, finiteTransport, transport, Iso.symm_inv] at result
  dsimp +instances only [L, clopenTensorRestriction, ProEt.clopenModuleRestriction] at result
  rw [hco, hcs] at result
  dsimp +instances only [cs, ff, Functor.FullyFaithful.preimageIso] at result
  have hsection (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V)) :
      cs.hom.hom.app (op V) s = (d.finite n).hom.hom.app (op V) s :=
    congrArg (fun f ↦ f.hom.app (op V) s) hcs
  change ∀ (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V)),
      ((fullyFaithfulSheafCompose (ProEt.topology U.toScheme)
        CommRingCat.fullyFaithfulForget₂ToRingCat).preimage
        (X := integralCoefficientCommRingSheaf l E U.toScheme n)
        (Y := rings.obj (integralCoefficientCommRingSheaf l E T n)) (d.finite n).hom).hom.app
        (op V) s = (d.finite n).hom.hom.app (op V) s at hsection
  obtain ⟨c', hc'⟩ := result
  refine ⟨c', ?_⟩
  intro M V s x
  have hh := hc' M V s x
  rw [hsection] at hh
  exact hh
end WeilConjectures
