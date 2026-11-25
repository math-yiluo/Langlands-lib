/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleRealization
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal

/-! # Normalized inverse image of the native coefficient ring

Source: Bhatt--Scholze, Section 6.8, and Stacks, Tag 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
variable (l : ℕ) [Fact l.Prime]

private instance forget_preservesKan {U V : Scheme.{u}} (g : U ⟶ V)
    {E : Type*} [Category.{u + 1} E] [HasColimitsOfSize.{u + 1, u + 1} E]
    (F : E ⥤ Type (u + 1)) [PreservesFilteredColimitsOfSize.{u + 1, u + 1} F] :
    F.PreservesLeftKanExtensions (proEtaleBaseChange g).op := by
  let B := proEtaleBaseChange g
  let : RepresentablyFlat B := flat_of_preservesFiniteLimits B
  let (Y : U.ProEtᵒᵖ) : IsFiltered (CostructuredArrow B.op Y) := inferInstance
  let : PreservesFilteredColimitsOfSize.{u, u + 1} F :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} F
  intro P
  exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise F P B.op

private def forgetPullbackIso {U V : Scheme.{u}} (g : U ⟶ V)
    {E : Type*} [Category.{u + 1} E] [HasColimitsOfSize.{u + 1, u + 1} E]
    [HasWeakSheafify (ProEt.topology U) E]
    (F : E ⥤ Type (u + 1))
    [(ProEt.topology U).HasSheafCompose F] [(ProEt.topology V).HasSheafCompose F]
    [(ProEt.topology U).PreservesSheafification F]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} F] :
    proEtaleSheafInverseImage g E ⋙ sheafCompose (ProEt.topology U) F ≅
      sheafCompose (ProEt.topology V) F ⋙ proEtaleSheafInverseImage g (Type (u + 1)) :=
  sheafPullbackForgetIso (ProEt.topology V) (ProEt.topology U) (proEtaleBaseChange g) F

private theorem forgetPullbackIso_transpose {U V : Scheme.{u}} (g : U ⟶ V)
    {E : Type*} [Category.{u + 1} E] [HasColimitsOfSize.{u + 1, u + 1} E]
    [HasWeakSheafify (ProEt.topology U) E]
    (F : E ⥤ Type (u + 1))
    [(ProEt.topology U).HasSheafCompose F] [(ProEt.topology V).HasSheafCompose F]
    [(ProEt.topology U).PreservesSheafification F]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} F]
    (A : Sheaf (ProEt.topology V) E) (B : Sheaf (ProEt.topology U) E)
    (f : A ⟶ (proEtaleSheafDirectImage g E).obj B) :
    (forgetPullbackIso g F).inv.app A ≫
        (sheafCompose (ProEt.topology U) F).map
          (((proEtaleSheafAdjunction g E).homEquiv A B).symm f) =
      ((proEtaleSheafAdjunction g (Type (u + 1))).homEquiv _ _).symm
        (⟨Functor.whiskerRight f.hom F⟩) := by
  apply ((proEtaleSheafAdjunction g (Type (u + 1))).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  have hu := sheafPullbackForgetIso_unit (ProEt.topology V) (ProEt.topology U)
    (proEtaleBaseChange g) F A
  change (sheafCompose (ProEt.topology V) F).map
      ((proEtaleSheafAdjunction g E).unit.app A) ≫
    (proEtaleSheafDirectImage g (Type (u + 1))).map
      ((forgetPullbackIso g F).hom.app A) = _ at hu
  let e := forgetPullbackIso g F
  let R := proEtaleSheafDirectImage g (Type (u + 1))
  let q := ((proEtaleSheafAdjunction g E).homEquiv A B).symm f
  calc
    _ = (sheafCompose (ProEt.topology V) F).map
          ((proEtaleSheafAdjunction g E).unit.app A) ≫
        R.map ((e.hom.app A ≫ e.inv.app A) ≫
          (sheafCompose (ProEt.topology U) F).map q) := by
      rw [← hu]
      apply Sheaf.hom_ext
      ext W x
      rfl
    _ = (sheafCompose (ProEt.topology V) F).map
          ((proEtaleSheafAdjunction g E).unit.app A) ≫
        R.map ((sheafCompose (ProEt.topology U) F).map q) := by
      rw [e.hom_inv_id_app, Category.id_comp]
    _ = (show (sheafCompose (ProEt.topology V) F).obj A ⟶
        R.obj ((sheafCompose (ProEt.topology U) F).obj B) from
          ⟨Functor.whiskerRight
            (((proEtaleSheafAdjunction g E).homEquiv A B) q).hom F⟩) := by
      apply Sheaf.hom_ext
      ext W x
      exact (ConcreteCategory.congr_hom (F.map_comp _ _) x).symm
    _ = _ := by simp only [q, Equiv.apply_symm_apply]

open CategoryTheory.MonoidalCategory Functor.LaxMonoidal
open scoped TensorProduct

private theorem section_mul (T : Scheme.{u}) [IsCommMonObj (abRing l T)]
    (W : T.ProEtᵒᵖ) (s t : (ringSheaf l T).obj.obj W) :
    s * t = ULift.up (s.down * t.down) := by
  let F := ProEtale.weilCoefficientsForgetAb l T
  let I := sheafToPresheaf (ProEt.topology T) Ab.{u + 1}
  let A := ProEtale.adicConstantSheaf l T
  have h := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose
    (ProEt.topology T) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}) A A) W
  simp only [NatTrans.comp_app] at h
  change ((μ I (F.obj A) (F.obj A)).app W ≫ (μ F A A).hom.app W ≫
    (F.map (MonObj.mul (X := A))).hom.app W).hom (s ⊗ₜ[ℤ] t) = _
  erw [← Category.assoc, h]
  have hm := congr_app (ProEtale.adicConstantSheaf_μ_comp_map_mul' (l := l) T) W
  exact congrArg (fun f ↦ f (s ⊗ₜ t)) hm

private theorem section_one (T : Scheme.{u}) [IsCommMonObj (abRing l T)]
    (W : T.ProEtᵒᵖ) :
    (1 : (ringSheaf l T).obj.obj W) = ULift.up 1 := by
  let R : CommRingCat.{u + 1} := (ringSheaf l T).obj.obj W
  let : CommRing R := CommRingCat.commRing R
  let z : R := ULift.up 1
  have he : (1 : R) * z = z := one_mul z
  have h := section_mul l T W (1 : R) z
  have hr : ULift.up ((1 : R).down * 1) = (1 : R) :=
    congrArg ULift.up (mul_one ((1 : R).down))
  exact hr.symm.trans (h.symm.trans he)

private def nativeDirectImageMap
    [∀ T : Scheme.{u}, IsCommMonObj (abRing l T)]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ringSheaf l V ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (ringSheaf l U) :=
  ⟨{ app := fun W ↦
        @CommRingCat.ofHom ((ringSheaf l V).obj.obj W)
          ((ringSheaf l U).obj.obj (op ((proEtaleBaseChange g).obj W.unop)))
          (CommRingCat.commRing _) (CommRingCat.commRing _)
        (show (ringSheaf l V).obj.obj W →+*
          (ringSheaf l U).obj.obj (op ((proEtaleBaseChange g).obj W.unop)) from
        { toFun := fun s ↦ ULift.up
            (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l
              (pullback.fst W.unop.hom g).base.hom s.down)
          map_one' := by rw [section_one, section_one]; rfl
          map_mul' := by
            intro s t
            let c := PadicAlgCl.locallyFiniteFunctionsCompAlgHom l
              (pullback.fst W.unop.hom g).base.hom
            have h₁ := congrArg (fun z : (ringSheaf l V).obj.obj W ↦ ULift.up (c z.down))
              (section_mul l V W s t)
            have h₂ := section_mul l U (op ((proEtaleBaseChange g).obj W.unop))
              (ULift.up (c s.down)) (ULift.up (c t.down))
            exact h₁.trans h₂.symm
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl })
     naturality := by
       intro W Z a
       ext s
       refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
       change s.down.1 (a.unop.left (pullback.fst _ g x)) =
         s.down.1 (pullback.fst _ g (((proEtaleBaseChange g).map a.unop).left x))
       have h : ((proEtaleBaseChange g).map a.unop).left ≫ pullback.fst _ g =
           pullback.fst _ g ≫ a.unop.left := pullback.lift_fst _ _ _
       have hx := congrArg (fun f ↦ f.base x) h
       exact congrArg (fun y ↦ s.down.1 y) hx.symm }⟩

private theorem nativeInverseImageMap_isIso
    [∀ T : Scheme.{u}, IsCommMonObj (abRing l T)]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    IsIso (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
      (nativeDirectImageMap l g)) := by
  let FM := forget (WeilCoefficients.{u} l)
  let FR := forget CommRingCat.{u + 1}
  let m := ProEtale.upperStarAdicConstantSheafHom l g
  have hset : IsIso
      (((proEtaleSheafAdjunction g (Type (u + 1))).homEquiv _ _).symm
        (show (sheafCompose (ProEt.topology V) FM).obj (ProEtale.adicConstantSheaf l V) ⟶
          (proEtaleSheafDirectImage g (Type (u + 1))).obj
            ((sheafCompose (ProEt.topology U) FM).obj (ProEtale.adicConstantSheaf l U)) from
          ⟨Functor.whiskerRight (ProEtale.adicConstantSheafToLowerStar l g).hom FM⟩)) := by
    rw [← forgetPullbackIso_transpose g FM]
    change IsIso ((forgetPullbackIso g FM).inv.app _ ≫
      (sheafCompose (ProEt.topology U) FM).map m)
    exact (((forgetPullbackIso g FM).app _).symm ≪≫
      (sheafCompose (ProEt.topology U) FM).mapIso
        (ProEtale.upperStarAdicConstantSheafIso l g)).isIso_hom
  let f := ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
    (nativeDirectImageMap l g)
  have heq := forgetPullbackIso_transpose g FR (ringSheaf l V) (ringSheaf l U)
    (nativeDirectImageMap l g)
  have hs : IsIso ((forgetPullbackIso g FR).inv.app (ringSheaf l V) ≫
      (sheafCompose (ProEt.topology U) FR).map f) := by
    rw [heq]
    exact hset
  have : IsIso ((sheafCompose (ProEt.topology U) FR).map f) :=
    IsIso.of_isIso_comp_left ((forgetPullbackIso g FR).inv.app _) _
  exact isIso_of_reflects_iso f (sheafCompose (ProEt.topology U) FR)

/-- The inverse image of locally finite coefficient functions, normalized on every section.
Source: Bhatt--Scholze, Section 6.8, Lemma 6.8.2 and Proposition 6.8.14;
Stacks, Tag 03D7.
(blueprint: lem-sf-native-coefficient-inverse-image).

Proof: precomposition with the first pullback projection defines a morphism of
coefficient ring sheaves to direct image. Its underlying map of sheaves of sets agrees
with the canonical map for module-valued adic coefficient sheaves. The latter's adjunct
is already an isomorphism. Inverse image commutes with forgetting to sets: base change
preserves finite limits, its opposite Kan-extension indexing categories are filtered,
and both forgetful functors preserve filtered colimits and sheafification. The
unit-compatible comparison therefore transfers the module isomorphism to the ring
adjunct, since forgetting reflects isomorphisms. The adjunction identity gives the
normalization formula. Pointwise extensionality and injectivity of the adjunction Hom
bijection give uniqueness. The argument also applies to empty test objects. -/
theorem native_coefficient_inverse_image
    [∀ T : Scheme.{u}, IsCommMonObj (abRing l T)]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ∃! c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (ringSheaf l V) ≅
        ringSheaf l U,
      ∀ (W : V.ProEtᵒᵖ) (s : (ringSheaf l V).obj.obj W)
        (x : ((proEtaleBaseChange g).obj W.unop).left),
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          c.hom).hom.app W s).down.1 x =
            s.down.1 ((pullback.fst W.unop.hom g).base x) := by
  let f := ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
    (nativeDirectImageMap l g)
  have : IsIso f := nativeInverseImageMap_isIso l g
  refine ⟨asIso f, ?_, ?_⟩
  · intro W s x
    change ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
        (nativeDirectImageMap l g))).hom.app W s).down.1 x = _
    rw [Equiv.apply_symm_apply]
    rfl
  · intro c hc
    apply Iso.ext
    apply ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).injective
    change ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _) c.hom =
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
          (nativeDirectImageMap l g))
    rw [Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    ext W s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact (hc W s x).trans (by rfl)

end WeilConjectures.LocallyFiniteAdicCompactSupport
