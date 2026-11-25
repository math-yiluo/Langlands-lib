/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafProjectionTensor
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat

set_option linter.privateModule false

/-! # Native open tensor comparisons on complexes

Source: Stacks 0GL1, 012Z and 0E8I; native open tensor proof steps 3--4.

The normalized restriction maps assemble to a natural sheaf comparison.
Totalizing it and the natural sheaf projection comparison gives the two
isomorphisms of unbounded cochain functors, before localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Mod.tensorLeft
  CategoryTheory.Mod.ihomAdjunction
  AlgebraicGeometry.ProEtaleWeilSheaf.tensorIhomAdjunction

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

private theorem ordinary_restriction_natural (l : ℕ) [Fact l.Prime]
    {X Y : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y)
    {M M' N N' : AlgebraicGeometry.ProEtale.AdicSheaf l Y}
    (f : M ⟶ M') (g : N ⟶ N') :
    (AlgebraicGeometry.ProEtale.adicUpperStar l j).map
        ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M') ≫
        (AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso l j N').hom.app M' =
      (AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso l j N).hom.app M ≫
        (Mod.tensorLeft ((AlgebraicGeometry.ProEtale.adicUpperStar l j).obj N)).map
          ((AlgebraicGeometry.ProEtale.adicUpperStar l j).map f) ≫
        (Mod.tensorLeftMap ((AlgebraicGeometry.ProEtale.adicUpperStar l j).map g)).app
          ((AlgebraicGeometry.ProEtale.adicUpperStar l j).obj M') := by
  have h := (AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso l j N).hom.naturality f
  dsimp only [Functor.comp_map,
    AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso,
    AlgebraicGeometry.ProEtale.adicUpperStar, Adjunction.modLeft,
    AlgebraicGeometry.ProEtale.adicUpperStarRingHom] at h
  rw [Functor.map_comp, Category.assoc]
  dsimp only [AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso,
    AlgebraicGeometry.ProEtale.adicUpperStar, Adjunction.modLeft,
    AlgebraicGeometry.ProEtale.adicUpperStarRingHom]
  rw [Mod.map_tensorLeftMap_app_tensorLeftCompMapModComapIso_hom_app]
  rw [← Category.assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [h, Category.assoc]
  rfl

namespace NativeOpenChainProof

end NativeOpenChainProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
private theorem comp_forget (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    {A B C : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.f = f.hom.f ≫ g.hom.f := rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem tensorFunctor_map_forget (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (A : ProEtaleWeilSheaf k₀ l X)
    {M N : ProEtaleWeilSheaf k₀ l X} (f : M ⟶ N) :
    ((tensorFunctor k₀ l X A).map f).hom.f =
      (Mod.tensorLeft A.carrier).map f.hom.f := rfl

private theorem ihomBifunctor_map_forget (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B)
    (N : ProEtaleWeilSheaf k₀ l X) :
    (((ihomBifunctor k₀ l X).map f.op).app N).hom.f =
      (Mod.ihomMap f.hom.f).app N.carrier := rfl

attribute [local implicit_reducible] Endofunctor.IsoAlgebra tensor tensorFunctor
attribute [local irreducible] ProEtale.adicUpperStar
attribute [local irreducible] nativeTensorMap Mod.tensorLeftMap

private theorem tensorMap_forget (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B)
    (M : ProEtaleWeilSheaf k₀ l X) :
    @Eq ((Mod.tensorLeft A.carrier).obj M.carrier ⟶
        (Mod.tensorLeft B.carrier).obj M.carrier)
      (((nativeTensorMap k₀ l X f).app M).hom.f)
      ((Mod.tensorLeftMap f.hom.f).app M.carrier) := by
  have h := NatTrans.congr_app
    ((conjugateEquiv (Mod.ihomAdjunction B.carrier)
      (Mod.ihomAdjunction A.carrier)).symm_apply_apply (Mod.tensorLeftMap f.hom.f)) M.carrier
  simp only [conjugateEquiv_symm_apply_app] at h
  simp only [nativeTensorMap, conjugateEquiv_symm_apply_app,
    comp_forget,
    tensorFunctor_map_forget, tensorIhomAdjunction_unit_app_hom_f,
    tensorIhomAdjunction_counit_app_hom_f, ihomBifunctor_map_forget]
  exact h

omit [Fact (ringChar k₀ ≠ l)] in
private theorem tensor_obj_a (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (A B : ProEtaleWeilSheaf k₀ l X) :
    @Eq (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (tensor k₀ l X A B).obj.a ((Mod.tensorLeft A.carrier).obj B.carrier) := rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem tensorFunctor_obj_a (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (A B : ProEtaleWeilSheaf k₀ l X) :
    @Eq (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((tensorFunctor k₀ l X A).obj B).obj.a
      ((Mod.tensorLeft A.carrier).obj B.carrier) := rfl

section GenericTransport

variable (e : ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) ⋙
        WeilSheaf.frobeniusPullback k₀ l U ≅
    WeilSheaf.frobeniusPullback k₀ l Z ⋙ ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
  (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
    (Endofunctor.IsoAlgebra.mapOfNatIso e).obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj N)
        ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M))
  (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
    ((ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier))

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
private theorem pull_map_forget {M N : ProEtaleWeilSheaf k₀ l Z} (f : M ⟶ N) :
    ((Endofunctor.IsoAlgebra.mapOfNatIso e).map f).hom.f =
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).map f.hom.f := rfl

include hrho in
omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
private theorem restriction_forget_eq (M N : ProEtaleWeilSheaf k₀ l Z) :
    @Eq
      ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj
            ((Mod.tensorLeft N.carrier).obj M.carrier) ⟶
        (Mod.tensorLeft ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj N.carrier)).obj
            ((ProEtale.adicUpperStar l
              (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj M.carrier))
      ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier) :=
  eq_of_heq (hrho M N)

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
private theorem pull_obj_carrier (M : ProEtaleWeilSheaf k₀ l Z) :
    ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M).carrier =
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj M.carrier := rfl

include hrho in
omit [IsOpenImmersion j] in
private theorem restriction_natural_underlying
    {M M' N N' : ProEtaleWeilSheaf k₀ l Z} (f : M ⟶ M') (g : N ⟶ N') :
    @Eq
      ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj
            ((Mod.tensorLeft N.carrier).obj M.carrier) ⟶
        (Mod.tensorLeft ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj N'.carrier)).obj
            ((ProEtale.adicUpperStar l
              (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj M'.carrier))
      ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).map
          ((Mod.tensorLeft N.carrier).map f.hom.f ≫
            ((nativeTensorMap k₀ l Z g).app M').hom.f) ≫
        (rho M' N').hom.hom.f)
      ((rho M N).hom.hom.f ≫
        (Mod.tensorLeft ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj N.carrier)).map
          ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).map f.hom.f) ≫
        ((nativeTensorMap k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).map g)).app
          ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M')).hom.f) := by
  let G := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  have hU :
      @Eq ((Mod.tensorLeft (G.obj N.carrier)).obj (G.obj M'.carrier) ⟶
          (Mod.tensorLeft (G.obj N'.carrier)).obj (G.obj M'.carrier))
        (((nativeTensorMap k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).map g)).app
          ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M')).hom.f)
        ((Mod.tensorLeftMap (G.map g.hom.f)).app (G.obj M'.carrier)) := by
    simpa only [pull_map_forget, pull_obj_carrier] using
      tensorMap_forget k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).map g)
        ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M')
  have hL := congrArg₂
    (fun (a : (Mod.tensorLeft N.carrier).obj M'.carrier ⟶
          (Mod.tensorLeft N'.carrier).obj M'.carrier)
        (b : G.obj ((Mod.tensorLeft N'.carrier).obj M'.carrier) ⟶
          (Mod.tensorLeft (G.obj N'.carrier)).obj (G.obj M'.carrier)) ↦
      G.map ((Mod.tensorLeft N.carrier).map f.hom.f ≫ a) ≫ b)
    (tensorMap_forget k₀ l Z g M') (restriction_forget_eq k₀ l j e rho hrho M' N')
  have hR := congrArg₂
    (fun (a : G.obj ((Mod.tensorLeft N.carrier).obj M.carrier) ⟶
          (Mod.tensorLeft (G.obj N.carrier)).obj (G.obj M.carrier))
        (b : (Mod.tensorLeft (G.obj N.carrier)).obj (G.obj M'.carrier) ⟶
          (Mod.tensorLeft (G.obj N'.carrier)).obj (G.obj M'.carrier)) ↦
      a ≫ (Mod.tensorLeft (G.obj N.carrier)).map (G.map f.hom.f) ≫ b)
    (restriction_forget_eq k₀ l j e rho hrho M N) hU
  exact hL.trans ((ordinary_restriction_natural l
    (Scheme.Hom.geometricFiberMap j (comp_over j _)) f.hom.f g.hom.f).trans hR.symm)

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
private theorem pull_obj_a (M : ProEtaleWeilSheaf k₀ l Z) :
    ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M).obj.a =
      (ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj M.obj.a := rfl

include hrho in
omit [IsOpenImmersion j] in
private theorem restriction_natural_general
    {M M' N N' : ProEtaleWeilSheaf k₀ l Z} (f : M ⟶ M') (g : N ⟶ N') :
    (Endofunctor.IsoAlgebra.mapOfNatIso e).map
        ((tensorFunctor k₀ l Z N).map f ≫ (nativeTensorMap k₀ l Z g).app M') ≫
        (rho M' N').hom =
      (rho M N).hom ≫
        (tensorFunctor k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj N)).map
          ((Endofunctor.IsoAlgebra.mapOfNatIso e).map f) ≫
        (nativeTensorMap k₀ l U ((Endofunctor.IsoAlgebra.mapOfNatIso e).map g)).app
          ((Endofunctor.IsoAlgebra.mapOfNatIso e).obj M') := by
  apply Endofunctor.IsoAlgebra.hom_ext
  simp only [comp_forget, pull_map_forget, tensorFunctor_map_forget]
  simpa only [tensor_obj_a, tensorFunctor_obj_a, pull_obj_a] using
    restriction_natural_underlying k₀ l j e rho hrho f g

end GenericTransport

omit [IsOpenImmersion j] in
private theorem restriction_natural_abstract
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    (e : ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) ⋙
          WeilSheaf.frobeniusPullback k₀ l U ≅
      WeilSheaf.frobeniusPullback k₀ l Z ⋙ ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    (hR : R = Endofunctor.IsoAlgebra.mapOfNatIso e)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier))
    {M M' N N' : ProEtaleWeilSheaf k₀ l Z} (f : M ⟶ M') (g : N ⟶ N') :
    R.map ((tensorFunctor k₀ l Z N).map f ≫ (nativeTensorMap k₀ l Z g).app M') ≫
        (rho M' N').hom =
      (rho M N).hom ≫ (tensorFunctor k₀ l U (R.obj N)).map (R.map f) ≫
        (nativeTensorMap k₀ l U (R.map g)).app (R.obj M') := by
  subst R
  exact restriction_natural_general k₀ l j e rho hrho f g

attribute [local irreducible] upperStar

omit [Fact (ringChar k₀ ≠ l)] [IsOpenImmersion j] in
private theorem upperStar_eq_transport :
    @Eq (ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
      (upperStar k₀ l j) (Endofunctor.IsoAlgebra.mapOfNatIso
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j _))) := by
  unfold upperStar
  rfl

private def sheafRestrictionIso_abstract
    (R : ProEtaleWeilSheaf k₀ l Z ⥤ ProEtaleWeilSheaf k₀ l U)
    (e : ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) ⋙
          WeilSheaf.frobeniusPullback k₀ l U ≅
      WeilSheaf.frobeniusPullback k₀ l Z ⋙ ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
    (hR : R = Endofunctor.IsoAlgebra.mapOfNatIso e)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      R.obj (tensor k₀ l Z N M) ≅ tensor k₀ l U (R.obj N) (R.obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) :
    nativeOpenSheafTensor k₀ l Z ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l U :=
  NatIso.ofComponents (fun MN ↦ rho MN.1 MN.2) (by
    intro MN MN' fg
    exact restriction_natural_abstract k₀ l j R e hR rho hrho fg.1 fg.2)

private def sheafRestrictionIso (s : NativeOpenTensorData k₀ l j) :
    nativeOpenSheafTensor k₀ l Z ⋙ upperStar k₀ l j ≅
      (upperStar k₀ l j).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U :=
  sheafRestrictionIso_abstract k₀ l j (upperStar k₀ l j)
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j _))
    (upperStar_eq_transport k₀ l j) s.sheafRestriction s.restriction_forget

end AlgebraicGeometry.ProEtaleWeilSheaf
