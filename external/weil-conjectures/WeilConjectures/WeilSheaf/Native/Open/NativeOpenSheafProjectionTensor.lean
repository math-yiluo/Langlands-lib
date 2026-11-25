/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-! # The equivariant sheaf open projection formula

Source: Stacks 0E8I, balanced generators and Frobenius reindexing.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u a b c d

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
attribute [local instance] Sheaf.symmetricCategory
namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] adicUpperStar

private theorem supported_tensor {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P B : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (hP : (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage P) :
    (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage (P ⊗ B) := by
  obtain ⟨Q, ⟨e⟩⟩ := hP
  exact ⟨_, ⟨asIso (((openImmersionLowerShriekProjectionMap
    (WeilCoefficients.{u} l) j).app Q).app B) ≪≫ whiskerRightIso e B⟩⟩

private theorem supported_module_tensor {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M N : AdicSheaf l X)
    (hM : (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage M.X) :
    (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage
      ((Mod.tensorLeft N).obj M).X := by
  let A := adicConstantSheaf l X
  let D := (Mod.tensorLeftDiagram A N).flip.obj M
  apply ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (AdicSheaf.forget X) (colimit.isColimit D))
  intro k
  cases k <;> exact supported_tensor j _ _ hM

private theorem supported_module_tensor_right {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M N : AdicSheaf l X)
    (hN : (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage N.X) :
    (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage
      ((Mod.tensorLeft N).obj M).X := by
  let A := adicConstantSheaf l X
  let D := (Mod.tensorLeftDiagram A N).flip.obj M
  apply ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (AdicSheaf.forget X) (colimit.isColimit D))
  intro k
  cases k
  · change (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage
      (M.X ⊗ (A ⊗ N.X))
    exact Functor.essImage.ofIso
      (whiskerRightIso (β_ N.X A) M.X ≪≫ β_ (A ⊗ N.X) M.X)
      (supported_tensor j (N.X ⊗ A) M.X (supported_tensor j N.X A hN))
  · exact Functor.essImage.ofIso (β_ _ _) (supported_tensor j N.X M.X hN)

private theorem module_counit_forget {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (N : AdicSheaf l X) :
    (adicOpenImmersionLowerShriekComparison l j).app ((adicUpperStar l j).obj N) ≫
      ((adicOpenImmersionLowerShriekAdjunction l j).counit.app N).hom =
        (openImmersionLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j).counit.app
          N.X := by
  let a := adicOpenImmersionLowerShriekAdjunction l j
  let b := openImmersionLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j
  let E := openImmersionLowerShriek (WeilCoefficients.{u} l) j
  change E.map (a.unit.app ((adicUpperStar l j).obj N)).hom ≫
    b.counit.app _ ≫ (a.counit.app N).hom = b.counit.app N.X
  have hn := b.counit.naturality (a.counit.app N).hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [← hn, ← E.map_comp_assoc]
  have ht := congrArg Mod.Hom.hom (a.right_triangle_components N)
  change (a.unit.app ((adicUpperStar l j).obj N)).hom ≫
    (upperStar (WeilCoefficients.{u} l) j).map (a.counit.app N).hom = 𝟙 _ at ht
  erw [ht, E.map_id, Category.id_comp]
  rfl

private theorem module_counit_isIso {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (N : AdicSheaf l X)
    (hN : (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage N.X) :
    IsIso ((adicOpenImmersionLowerShriekAdjunction l j).counit.app N) := by
  have : IsIso ((openImmersionLowerShriekUpperStarAdjunction
      (WeilCoefficients.{u} l) j).counit.app N.X) :=
    (openImmersionLowerShriekUpperStarAdjunction
      (WeilCoefficients.{u} l) j).isIso_counit_app_iff_mem_essImage.mpr hN
  have : IsIso ((adicOpenImmersionLowerShriekComparison l j).app
      ((adicUpperStar l j).obj N) ≫
        ((adicOpenImmersionLowerShriekAdjunction l j).counit.app N).hom) := by
    rw [module_counit_forget]
    infer_instance
  have h := IsIso.of_isIso_comp_left ((adicOpenImmersionLowerShriekComparison l j).app
    ((adicUpperStar l j).obj N))
    ((adicOpenImmersionLowerShriekAdjunction l j).counit.app N).hom
  have : IsIso ((AdicSheaf.forget X).map
      ((adicOpenImmersionLowerShriekAdjunction l j).counit.app N)) := h
  exact isIso_of_reflects_iso _ (AdicSheaf.forget X)

private theorem extension_supported {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : AdicSheaf l U) :
    (openImmersionLowerShriek (WeilCoefficients.{u} l) j).essImage
      ((adicOpenImmersionLowerShriek l j).obj M).X := by
  exact ⟨M.X, ⟨(asIso (adicOpenImmersionLowerShriekComparison l j)).app M⟩⟩

end AlgebraicGeometry.ProEtale

namespace NativeOpenProjectionProof
variable {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
  {E : C ⥤ D} {R : D ⥤ C}

private def bifunctorIsoOfComponents {A B V : Type*}
    [Category* A] [Category* B] [Category* V] (F G : A ⥤ B ⥤ V)
    (e : ∀ M N, (F.obj M).obj N ≅ (G.obj M).obj N)
    (h : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      (F.map f).app N ≫ (F.obj M').map g ≫ (e M' N').hom =
        (e M N).hom ≫ (G.map f).app N ≫ (G.obj M').map g) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (e M) (by
    intro N N' g
    simpa using h (𝟙 M) g)) (by
      intro M M' f
      apply NatTrans.ext
      funext N
      simpa using h f (𝟙 N))

private def restrictionCurried
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (r : Functor.uncurry.obj T' ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj T) :
    (((Functor.whiskeringLeft₂ C).obj R).obj R).obj T ≅
      (Functor.postcompose₂.obj R).obj T' :=
  bifunctorIsoOfComponents _ _ (fun M N ↦ (r.app (M, N)).symm) (by
    intro M M' N N' f g
    change (T.map (R.map f)).app (R.obj N) ≫
        (T.obj (R.obj M')).map (R.map g) ≫ (r.app (M', N')).inv =
      (r.app (M, N)).inv ≫ R.map ((T'.map f).app N) ≫ R.map ((T'.obj M').map g)
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      Functor.prod_map, Functor.uncurry_obj_map, Functor.map_comp,
      Category.assoc, Iso.symm_hom, Iso.app_inv] using
        r.inv.naturality (Prod.mkHom f g))

private theorem projectionMap_isIso (adj : E ⊣ R) [IsIso adj.unit]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj R).obj R).obj T ≅
      (Functor.postcompose₂.obj R).obj T')
    (hc : ∀ M N, IsIso (adj.counit.app ((T'.obj (E.obj M)).obj N))) (M : C) (N : D) :
    IsIso (((adj.projectionMap R T T' δ.hom).app M).app N) := by
  rw [Adjunction.projectionMap_app_app, adj.homEquiv_counit]
  change IsIso (E.map _ ≫ adj.counit.app ((T'.obj (E.obj M)).obj N))
  have := hc M N
  infer_instance

private def projectionIso (adj : E ⊣ R) [IsIso adj.unit]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj R).obj R).obj T ≅
      (Functor.postcompose₂.obj R).obj T')
    (hc : ∀ M N, IsIso (adj.counit.app ((T'.obj (E.obj M)).obj N))) :
    E.prod (𝟭 D) ⋙ Functor.uncurry.obj T' ≅
      (𝟭 C).prod R ⋙ Functor.uncurry.obj T ⋙ E := by
  let p := adj.projectionMap R T T' δ.hom
  have hi (M : C) (N : D) : IsIso ((p.app M).app N) :=
    projectionMap_isIso adj T T' δ hc M N
  have (M : C) : IsIso (p.app M) := NatIso.isIso_of_isIso_app _
  have : IsIso p := NatIso.isIso_of_isIso_app _
  let q := Functor.uncurry.mapIso (asIso p)
  exact NatIso.ofComponents (fun MN ↦ (q.app MN).symm) (by
    intro MN MN' fg
    have h := q.inv.naturality fg
    change ((T'.map (E.map fg.1)).app MN.2 ≫
        (T'.obj (E.obj MN'.1)).map fg.2) ≫ q.inv.app MN' =
      q.inv.app MN ≫ E.map ((T.map fg.1).app (R.obj MN.2)) ≫
        E.map ((T.obj MN'.1).map (R.map fg.2)) at h
    simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.prod_obj, Functor.id_map, Functor.id_obj, Functor.map_comp,
      Category.assoc, Iso.symm_hom, Iso.app_inv] using h)

private def projectionIsoOther (adj : E ⊣ R) [IsIso adj.unit]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj R).obj R).obj T ≅
      (Functor.postcompose₂.obj R).obj T')
    (hc : ∀ M N, IsIso (adj.counit.app ((T'.obj N).obj (E.obj M)))) :
    (𝟭 D).prod E ⋙ Functor.uncurry.obj T' ≅
      R.prod (𝟭 C) ⋙ Functor.uncurry.obj T ⋙ E := by
  let δ' : (((Functor.whiskeringLeft₂ C).obj R).obj R).obj T.flip ≅
      (Functor.postcompose₂.obj R).obj T'.flip := (flipFunctor _ _ _).mapIso δ
  let g := projectionIso adj T.flip T'.flip δ' hc
  exact NatIso.ofComponents (fun NM ↦ g.app (NM.2, NM.1)) (by
    intro NM NM' fg
    change ((T'.map fg.1).app (E.obj NM.2) ≫
        (T'.obj NM'.1).map (E.map fg.2)) ≫ _ =
      _ ≫ E.map ((T.map (R.map fg.1)).app NM.2 ≫
        (T.obj (R.obj NM'.1)).map fg.2)
    rw [← (T'.map fg.1).naturality (E.map fg.2),
      ← (T.map (R.map fg.1)).naturality fg.2]
    exact g.hom.naturality (Prod.mkHom fg.2 fg.1))
private theorem nonemptyProjections (adj : E ⊣ R) [IsIso adj.unit]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (r : Functor.uncurry.obj T' ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj T)
    (hc : ∀ M N, IsIso (adj.counit.app ((T'.obj (E.obj M)).obj N)))
    (hc' : ∀ M N, IsIso (adj.counit.app ((T'.obj N).obj (E.obj M)))) :
    Nonempty (E.prod (𝟭 D) ⋙ Functor.uncurry.obj T' ≅
      (𝟭 C).prod R ⋙ Functor.uncurry.obj T ⋙ E) ∧
    Nonempty ((𝟭 D).prod E ⋙ Functor.uncurry.obj T' ≅
      R.prod (𝟭 C) ⋙ Functor.uncurry.obj T ⋙ E) := by
  let δ := restrictionCurried T T' r
  exact ⟨⟨projectionIso adj T T' δ hc⟩, ⟨projectionIsoOther adj T T' δ hc'⟩⟩

private theorem transpose_isIso (adj : E ⊣ R) {A : C} {X : D}
    (t : A ⟶ R.obj X) [IsIso t] [IsIso (adj.counit.app X)] :
    IsIso ((adj.homEquiv A X).symm t) := by
  rw [adj.homEquiv_counit]
  infer_instance

end NativeOpenProjectionProof

section RestrictionNaturality

attribute [local irreducible] Mod.tensorLeft Mod.ihomAdjunction
  AlgebraicGeometry.ProEtaleWeilSheaf.tensorIhomAdjunction

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

end AlgebraicGeometry.ProEtaleWeilSheaf

end RestrictionNaturality

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

attribute [local implicit_reducible] tensor tensorFunctor

attribute [local irreducible] Scheme.Hom.geometricFiberMap
  Scheme.Hom.geometricGaloisFrobenius Mod.tensorLeft Mod.ihomAdjunction
  nativeTensorMap tensorIhomAdjunction

omit [Fact (ringChar k₀ ≠ l)] in
private theorem sheafUnit_isIso
    (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
    (hu : ∀ M, (adj.unit.app M).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier) :
    IsIso adj.unit := by
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
  have hunit (M : ProEtaleWeilSheaf k₀ l U) : IsIso (adj.unit.app M) := by
    have : IsIso (F.map (adj.unit.app M)) := by
      change IsIso ((adj.unit.app M).hom.f)
      rw [hu]
      infer_instance
    exact isIso_of_reflects_iso _ F
  exact NatIso.isIso_of_isIso_app _

omit [Fact (ringChar k₀ ≠ l)] in
private theorem sheafTensorCounits_isIso
    (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
    (hc : ∀ N, (adj.counit.app N).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier) :
    (∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      IsIso (adj.counit.app (tensor k₀ l Z N ((extensionByZero k₀ l j).obj M)))) ∧
    (∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      IsIso (adj.counit.app (tensor k₀ l Z ((extensionByZero k₀ l j).obj M) N))) := by
  let E := extensionByZero k₀ l j
  let v := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  let F' := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  have hs (M : ProEtaleWeilSheaf k₀ l U) :
      (ProEtale.openImmersionLowerShriek (WeilCoefficients.{u} l) v).essImage
        (E.obj M).carrier.X := ProEtale.extension_supported v M.carrier
  have hcs (N : ProEtaleWeilSheaf k₀ l Z)
      (hN : (ProEtale.openImmersionLowerShriek (WeilCoefficients.{u} l) v).essImage
        N.carrier.X) : IsIso (adj.counit.app N) := by
    have : IsIso (F'.map (adj.counit.app N)) := by
      change IsIso ((adj.counit.app N).hom.f)
      rw [hc]
      exact ProEtale.module_counit_isIso v N.carrier hN
    exact isIso_of_reflects_iso _ F'
  constructor
  · intro M N
    exact hcs _ (ProEtale.supported_module_tensor v (E.obj M).carrier N.carrier (hs M))
  · intro M N
    exact hcs _ (ProEtale.supported_module_tensor_right v N.carrier (E.obj M).carrier (hs M))

private theorem tensor_bifunctor_obj_obj (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M N : ProEtaleWeilSheaf k₀ l X) :
    (((nativeTensorBifunctor k₀ l X).flip.obj M).obj N) = tensor k₀ l X N M := rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem sheafProjectionGamma
    (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j) [IsIso adj.unit]
    (hct : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      IsIso (adj.counit.app (tensor k₀ l Z N ((extensionByZero k₀ l j).obj M))))
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M)) :
    ∃ gamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
        (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M),
      ∀ M N, HEq (adj.homEquiv _ _ ((gamma M N).inv))
        ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
          (rho ((extensionByZero k₀ l j).obj M) N).inv) := by
  let p (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z) :
      (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M) ⟶
        tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) :=
    (adj.homEquiv _ _).symm
      ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
        (rho ((extensionByZero k₀ l j).obj M) N).inv)
  have hp (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z) :
      IsIso (p M N) := by
    have := hct M N
    exact NativeOpenProjectionProof.transpose_isIso adj _
  refine ⟨fun M N ↦ (asIso (p M N)).symm, ?_⟩
  intro M N
  exact heq_of_eq ((adj.homEquiv _ _).apply_symm_apply _)

/-- The two orientations of the sheaf projection formula, with the first
orientation normalized by the specified open unit.

Source: Stacks Project, sites-modules.tex, Tag 0E8I,
lemma-j-shriek-and-tensor; step 2 of the native open tensor argument.
(blueprint: lem-sf-native-open-sheaf-projection-tensor).

Proof: the ordinary sheaf projection formula shows that tensoring a sheaf
supported on the open with any sheaf preserves that support. The essential
image of ordinary extension by zero is closed under colimits. Apply this to
the two objects in the relative module tensor coequalizer, in either order.
The comparison between module extension and sheaf extension and the triangle
identity identify the underlying module counit with the sheaf counit, so the
module counit is invertible on both tensor objects. Faithful conservative
forgetting and the specified unit and counit normalizations give the same
facts for Weil sheaves.

The normalized restriction comparisons are natural: after faithful forgetting,
their naturality is the ordinary balanced restriction comparison's naturality
in each module. Form the natural adjunction projection map with their inverses.
Its transpose is tensoring the unit followed by inverse restriction comparison;
this is invertible, as is the counit on its target by the support calculation.
Consequently the projection map is invertible. Its inverse gives the first
natural isomorphism. The pointwise adjunction-transpose construction gives
gamma and its required adjunct identity. Apply the same construction to the flipped tensor
bifunctor and
exchange the input variables to obtain the other natural isomorphism. Empty
opens and zero objects are included by the colimit and adjunction arguments;
no quasi-compactness, complex or K-flatness hypothesis is used. -/
theorem native_open_sheaf_projection_tensor
    (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
    (hu : ∀ M, (adj.unit.app M).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier)
    (hc : ∀ N, (adj.counit.app N).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) :
    ∃ gamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
        (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M),
      (∀ M N, HEq (adj.homEquiv _ _ ((gamma M N).inv))
        ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
          (rho ((extensionByZero k₀ l j).obj M) N).inv)) ∧
      Nonempty (nativeOpenSheafLeft k₀ l j ≅ nativeOpenSheafRight k₀ l j) ∧
      Nonempty ((𝟭 (ProEtaleWeilSheaf k₀ l Z)).prod (extensionByZero k₀ l j) ⋙
          nativeOpenSheafTensor k₀ l Z ≅
        (upperStar k₀ l j).prod (𝟭 (ProEtaleWeilSheaf k₀ l U)) ⋙ nativeOpenSheafTensor k₀ l U ⋙
          extensionByZero k₀ l j) := by
  have : IsIso adj.unit := sheafUnit_isIso k₀ l j adj hu
  obtain ⟨hct, hct'⟩ := sheafTensorCounits_isIso k₀ l j adj hc
  obtain ⟨gamma, hgamma⟩ := sheafProjectionGamma k₀ l j adj hct rho
  have hcT (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z) :
      IsIso (adj.counit.app
        (((nativeTensorBifunctor k₀ l Z).flip.obj ((extensionByZero k₀ l j).obj M)).obj N)) := by
    rw [tensor_bifunctor_obj_obj]
    exact hct M N
  have hcT' (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z) :
      IsIso (adj.counit.app
        (((nativeTensorBifunctor k₀ l Z).flip.obj N).obj ((extensionByZero k₀ l j).obj M))) := by
    rw [tensor_bifunctor_obj_obj]
    exact hct' M N
  have hn := NativeOpenProjectionProof.nonemptyProjections adj
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    (sheafRestrictionIso_abstract k₀ l j (upperStar k₀ l j)
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j _))
      (upperStar_eq_transport k₀ l j) rho hrho) hcT hcT'
  exact ⟨gamma, hgamma, hn⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
