/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.CategoryTheory.ArrowHEq.ArrowHEq

/-! # Completed-to-native scalar compatibility for compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.PurCompactSupport
private def localOpenMap (R S : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (ax : R.ring X ⟶ S.ring X) (az : R.ring c.Z ⟶ S.ring c.Z)
    (hi : (R.pull c.i).hom ≫ ax =
      (proEtaleSheafInverseImage c.i CommRingCat.{u + 1}).map az ≫ (S.pull c.i).hom) :=
  letI := proEtaleRingRestrictionPullbackInv_isIso
    c.i (R.ring c.Z) (S.ring c.Z) (R.ring X) (S.ring X)
      az ax (R.pull c.i) (S.pull c.i) hi
  ((mateEquiv (openAdjunction S c.i) (openAdjunction R c.i)).symm
    (TwoSquare.mk _ _ _ _ (inv (proEtaleRingRestrictionPullbackInv
      c.i (R.ring c.Z) (S.ring c.Z) (R.ring X) (S.ring X)
        az ax (R.pull c.i) (S.pull c.i) hi))))

private def localComparison (R S : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (ax : R.ring X ⟶ S.ring X) (az : R.ring c.Z ⟶ S.ring c.Z)
    (ay : R.ring Y ⟶ S.ring Y)
    (hi : (R.pull c.i).hom ≫ ax =
      (proEtaleSheafInverseImage c.i CommRingCat.{u + 1}).map az ≫ (S.pull c.i).hom)
    (hg : (R.pull c.g).hom ≫ az =
      (proEtaleSheafInverseImage c.g CommRingCat.{u + 1}).map ay ≫ (S.pull c.g).hom)
    (hIso : IsIso (localOpenMap R S c ax az hi)) :
    image R c ⋙ pbcDerivedExtend ay ⟶ pbcDerivedExtend ax ⋙ image S c :=
  letI := hIso
  ((mateEquiv (pbcDerivedScalarAdjunction ax) (pbcDerivedScalarAdjunction ay)).symm
    (TwoSquare.mk _ _ _ _ (by
      change (pbcDerivedRestrict ax ⋙ image R c ⟶ image S c ⋙ pbcDerivedRestrict ay)
      dsimp only [pbcDerivedRestrict, pbcRestrict]
      exact
      (Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (asIso (localOpenMap R S c ax az hi)))
          (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)) ≪≫
        Functor.isoWhiskerLeft (openExtension S c.i).mapDerivedCategory
          (proEtaleRingRestrictionDerivedDirectImage c.g
            (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
            ay az (R.pull c.g) (S.pull c.g) hg).symm).hom)))

private theorem localComparison_heq (R S : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (ax ax' : R.ring X ⟶ S.ring X) (az az' : R.ring c.Z ⟶ S.ring c.Z)
    (ay ay' : R.ring Y ⟶ S.ring Y)
    (hi : (R.pull c.i).hom ≫ ax =
      (proEtaleSheafInverseImage c.i CommRingCat.{u + 1}).map az ≫ (S.pull c.i).hom)
    (hg : (R.pull c.g).hom ≫ az =
      (proEtaleSheafInverseImage c.g CommRingCat.{u + 1}).map ay ≫ (S.pull c.g).hom)
    (hi' : (R.pull c.i).hom ≫ ax' =
      (proEtaleSheafInverseImage c.i CommRingCat.{u + 1}).map az' ≫ (S.pull c.i).hom)
    (hg' : (R.pull c.g).hom ≫ az' =
      (proEtaleSheafInverseImage c.g CommRingCat.{u + 1}).map ay' ≫ (S.pull c.g).hom)
    (hax : ax = ax') (haz : az = az') (hay : ay = ay')
    (hIso : IsIso (localOpenMap R S c ax az hi))
    (hIso' : IsIso (localOpenMap R S c ax' az' hi'))
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    HEq ((localComparison R S c ax az ay hi hg hIso).app M)
      ((localComparison R S c ax' az' ay' hi' hg' hIso').app M) := by
  subst ax' az' ay'
  rfl

private theorem comparison_heq {R S : Coefficients.{u}} (a b : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hX : a.map X = b.map X) (hY : a.map Y = b.map Y)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    HEq ((comparison a c).app M) ((comparison b c).app M) := by
  have hZ : a.map c.Z = b.map c.Z := by
    apply (cancel_epi (R.pull c.g).hom).1
    rw [a.square c.g, b.square c.g, hY]
  exact localComparison_heq R S c (a.map X) (b.map X) (a.map c.Z) (b.map c.Z)
    (a.map Y) (b.map Y) (a.square c.i) (a.square c.g) (b.square c.i) (b.square c.g)
    hX hZ hY (openRestrictionMap_isIso a c.i) (openRestrictionMap_isIso b c.i) M

private theorem normalization_tensor {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d)
    (M : DerivedCategory (pbcModules W R)) :
    (pbcReductionNormalization a b d h M).hom =
      (tensorComposition a b d h).hom.app M := by
  let adja := pbcDerivedScalarAdjunction a
  let adjb := pbcDerivedScalarAdjunction b
  let adjd := pbcDerivedScalarAdjunction d
  let e := pbcDerivedRestrictComp a b d h
  let adj := (adja.comp adjb).ofNatIsoRight e
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ (pbcReductionNormalizationHom a b d h M) =
    adj.homEquiv _ _ ((adj.leftAdjointUniq adjd).hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [adj, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    pbcReductionNormalizationHom, pbcReductionTransition, adja, adjb,
    Equiv.trans_apply, e, adjd, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem normalization_congr {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d d' : R ⟶ T)
    (h : a ≫ b = d) (h' : a ≫ b = d') (hd : d = d')
    (M : DerivedCategory (pbcModules W R)) :
    ArrowHEq (pbcReductionNormalization a b d h M).hom
      (pbcReductionNormalization a b d' h' M).hom := by
  cases hd
  exact ArrowHEq.refl (pbcReductionNormalization a b d h M).hom

private def compositeChange {R S T : Coefficients.{u}}
    (a : Change R S) (b : Change S T) : Change R T where
  map W := a.map W ≫ b.map W
  square g := by
    rw [← Category.assoc, a.square g, Category.assoc, b.square g]
    simp only [Functor.map_comp, Category.assoc]

private theorem comparison_composition_local {R S T : Coefficients.{u}}
    (a : Change R S) (b : Change S T) (d : Change R T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hx : a.map X ≫ b.map X = d.map X)
    (hy : a.map Y ≫ b.map Y = d.map Y)
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image T c).map (pbcReductionNormalization
          (a.map X) (b.map X) (d.map X) hx M).hom =
      (pbcReductionNormalization (a.map Y) (b.map Y) (d.map Y) hy
          ((image R c).obj M)).hom ≫ (comparison d c).app M := by
  let e := compositeChange a b
  have hc := comparison_composition a b e (fun _ ↦ rfl) c M
  have hxnorm := normalization_tensor (a.map X) (b.map X) (e.map X) rfl M
  have hynorm := normalization_tensor (a.map Y) (b.map Y) (e.map Y) rfl
    ((image R c).obj M)
  rw [← hxnorm, ← hynorm] at hc
  have hnx := normalization_congr (a.map X) (b.map X) (d.map X) (e.map X)
    hx rfl hx.symm M
  have hny := normalization_congr (a.map Y) (b.map Y) (e.map Y) (d.map Y)
    rfl hy hy ((image R c).obj M)
  have hbeta : ArrowHEq ((comparison e c).app M) ((comparison d c).app M) :=
    ⟨congrArg (fun φ ↦ (pbcDerivedExtend φ).obj ((image R c).obj M)) hy,
      congrArg (fun φ ↦ (image T c).obj ((pbcDerivedExtend φ).obj M)) hx,
      comparison_heq e d c hx hy M⟩
  exact eq_of_heq (((ArrowHEq.refl _).comp
    ((ArrowHEq.refl _).comp (hnx.map (image T c)))).trans
      ((show ArrowHEq _ _ from ⟨rfl, rfl, heq_of_eq hc⟩).trans
        (hny.comp hbeta))).heq

private theorem normalization_inv_congr {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b b' : S ⟶ T) (d d' : R ⟶ T)
    (h : a ≫ b = d) (h' : a ≫ b' = d') (hb : b = b') (hd : d = d')
    (M : DerivedCategory (pbcModules W R)) :
    ArrowHEq (pbcReductionNormalization a b d h M).inv
      (pbcReductionNormalization a b' d' h' M).inv := by
  cases hb
  cases hd
  exact ArrowHEq.refl (pbcReductionNormalization a b d h M).inv

private theorem extend_map_congr {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a b : R ⟶ S) (hab : a = b)
    {M N : DerivedCategory (pbcModules W R)} (v : M ⟶ N) :
    ArrowHEq ((pbcDerivedExtend a).map v) ((pbcDerivedExtend b).map v) := by
  subst b
  exact ArrowHEq.refl _

private theorem castArrowNormalization {C : Type*} [Category C]
    {A B A' B' : C} (f : A' ⟶ B') (hA : A = A') (hB : B' = B) :
    ArrowHEq (eqToHom hA ≫ f ≫ eqToHom hB) f := by
  cases hA
  cases hB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ArrowHEq.refl f

private theorem comparison_completion {R S T : Coefficients.{u}}
    (a : Change R S) (b : Change S T) (d : Change R T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hx : a.map X ≫ b.map X = d.map X)
    (hy : a.map Y ≫ b.map Y = d.map Y)
    (M : DerivedCategory (pbcModules X (R.ring X)))
    (N' : DerivedCategory (pbcModules X (S.ring X)))
    (v : (pbcDerivedExtend (a.map X)).obj M ⟶ N') :
    (pbcReductionNormalization (a.map Y) (b.map Y) (d.map Y) hy
        ((image R c).obj M)).inv ≫
      (pbcDerivedExtend (b.map Y)).map
        ((comparison a c).app M ≫ (image S c).map v) ≫
      (comparison b c).app N' =
    (comparison d c).app M ≫ (image T c).map
      ((pbcReductionNormalization (a.map X) (b.map X) (d.map X) hx M).inv ≫
        (pbcDerivedExtend (b.map X)).map v) := by
  let nx := pbcReductionNormalization (a.map X) (b.map X) (d.map X) hx M
  let ny := pbcReductionNormalization (a.map Y) (b.map Y) (d.map Y) hy
    ((image R c).obj M)
  have hc := comparison_composition_local a b d c hx hy M
  have hc' : ny.inv ≫ (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) =
      (comparison d c).app M ≫ (image T c).map nx.inv := by
    change _ ≫ _ ≫ (image T c).map nx.hom = ny.hom ≫ _ at hc
    have hh := congrArg (fun z ↦ ny.inv ≫ z ≫ (image T c).map nx.inv) hc
    have hcancel : (image T c).map nx.hom ≫ (image T c).map nx.inv = 𝟙 _ :=
      ((image T c).mapIso nx).hom_inv_id
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, hcancel, Category.comp_id] using hh
  calc
    _ = (ny.inv ≫ (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M)) ≫
        (image T c).map ((pbcDerivedExtend (b.map X)).map v) := by
      have hn := (comparison b c).naturality v
      dsimp only [Functor.comp_map] at hn
      simp only [Functor.map_comp, Category.assoc]
      rw [hn]
    _ = _ := by
      rw [hc']
      simp only [Functor.map_comp, Category.assoc, nx]

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open _root_.WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

set_option backward.isDefEq.respectTransparency false in
omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Ordinary completed-to-native scalar mates respect finite completed coefficient change.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 07A6, pasting of scalar mates.

Proof: the completed coefficient inclusion followed by the native coefficient map
agrees with the original native coefficient map at X and Y by `coefficient_scalar`.
Compatibility with pullback gives the same equation at the intermediate scheme of
the compactification. Apply the composition equation for the proper/open scalar
mate, with the balanced ordinary tensor associators. Their normalization agrees with
`pbcReductionNormalization`, since both are conjugate to identity on restricted
sections and preserve the scalar adjunction unit. Naturality of the second scalar
mate moves the ordinary-to-completed comparison through it. Functoriality combines
this map with the finite completed scalar mate, giving the left side. The direct
scalar mate and compact support of the same completion map give the right side.
This is an equality in the ambient ordinary derived category for every M; no stage
functor, rational comparison, or integral realization boundary occurs.
(blueprint: lem-sf-native-completed-scalar-mate-transition). -/
theorem nativeScalarComponent_transition [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (change : ∀ j : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) j)) (nativeCoefficients l))
    (hs : ∀ j, (change j).map X = (source.coefficient j).integralMap l X)
    (ht : ∀ j, (change j).map Y = (target.coefficient j).integralMap l Y)
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (M : DerivedCategory (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) i) X)) :
    supportScalarTransition l c target i E h M ≫
        nativeScalarComponent l c source target E (change E) (hs E) (ht E)
          ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
            (Coefficient.{u} l (PadicAlgCl l) E)
            (coefficientInclusion l (PadicAlgCl l) i E h) X).obj M) =
      nativeScalarComponent l c source target i (change i) (hs i) (ht i) M ≫
        (PurCompactSupport.image (nativeCoefficients l) c).map
          (nativeScalarTransition l X source i E h M)  := by
  let a := completedChange l (Coefficient.{u} l (PadicAlgCl l) i)
    (Coefficient.{u} l (PadicAlgCl l) E) (coefficientInclusion l (PadicAlgCl l) i E h)
  let b := change E
  let d := change i
  have hx : a.map X ≫ b.map X = d.map X := by
    dsimp only [a, b, d, completedChange]
    rw [hs E, hs i]
    exact source.coefficient_scalar i E h
  have hy : a.map Y ≫ b.map Y = d.map Y := by
    dsimp only [a, b, d, completedChange]
    rw [ht E, ht i]
    exact target.coefficient_scalar i E h
  let v := (completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) i)
    (Coefficient.{u} l (PadicAlgCl l) E)
    (coefficientInclusion l (PadicAlgCl l) i E h)).app M
  have hc := comparison_completion a b d c hx hy M _ v
  have hny := normalization_inv_congr (a.map Y)
    ((target.coefficient E).integralMap l Y) (b.map Y)
    ((target.coefficient i).integralMap l Y) (d.map Y)
    (target.coefficient_scalar i E h) hy (ht E).symm (ht i).symm
      ((image (completed l (Coefficient.{u} l (PadicAlgCl l) i)) c).obj M)
  have hby := extend_map_congr ((target.coefficient E).integralMap l Y) (b.map Y)
    (ht E).symm ((comparison a c).app M ≫
      (image (completed l (Coefficient.{u} l (PadicAlgCl l) E)) c).map v)
  have hnE : ArrowHEq
      (nativeScalarComponent l c source target E (change E) (hs E) (ht E)
        ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
          (Coefficient.{u} l (PadicAlgCl l) E)
          (coefficientInclusion l (PadicAlgCl l) i E h) X).obj M))
      ((comparison b c).app _) := castArrowNormalization _ _ _
  have hni : ArrowHEq
      (nativeScalarComponent l c source target i (change i) (hs i) (ht i) M)
      ((comparison d c).app M) := castArrowNormalization _ _ _
  have hnx := normalization_inv_congr (a.map X)
    ((source.coefficient E).integralMap l X) (b.map X)
    ((source.coefficient i).integralMap l X) (d.map X)
    (source.coefficient_scalar i E h) hx (hs E).symm (hs i).symm M
  have hbx := extend_map_congr ((source.coefficient E).integralMap l X) (b.map X)
    (hs E).symm v
  have hsupport : ArrowHEq (supportScalarTransition l c target i E h M) _ :=
    hny.comp hby
  have htransition : ArrowHEq (nativeScalarTransition l X source i E h M) _ :=
    hnx.comp hbx
  have hlhs := hsupport.comp hnE
  have hrhs := hni.comp (htransition.map (image (nativeCoefficients l) c))
  have hc' := (Category.assoc _ _ _).trans hc
  exact eq_of_heq (hlhs.trans
    ((show ArrowHEq _ _ from ⟨rfl, rfl, heq_of_eq hc'⟩).trans hrhs.symm)).heq

end WeilConjectures.LocallyFiniteAdicCompactSupport
