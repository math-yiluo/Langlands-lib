/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluation of inverse image on a ringed sequence site

Source: Zheng, Construction 4.1; the sectionwise coextension argument.
(blueprint: lem-sf-sequence-module-pullback-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r k h d w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace WeilConjectures.SequenceModuleEvaluation
variable {C : Type c} [Category.{v} C]
variable [UnivLE.{c, r}] [UnivLE.{v, r}] [UnivLE.{max c v, r}]
private local instance sliceContinuous (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  letI : EssentiallySmall.{max c v} C := essentiallySmallSelf.{v, v, c} C
  evaluationContinuous.{c, v, max c v} J n
variable (A : (ℕ × C)ᵒᵖ ⥤ RingCat.{r}) (n : ℕ)
private def hor (V : (ℕ × C)ᵒᵖ) (h : n ≤ V.unop.1) :
    V ⟶ op (n, V.unop.2) := (Prod.mkHom (homOfLE h) (𝟙 V.unop.2)).op
private abbrev coValue (M : PresheafOfModules.{r} ((Prod.sectR n C).op ⋙ A))
    (V : (ℕ × C)ᵒᵖ) : ModuleCat.{r} (A.obj V) :=
  ModuleCat.of (A.obj V)
    (∀ h : PLift (n ≤ V.unop.1),
      (ModuleCat.restrictScalars (A.map (hor n V h.down)).hom).obj (M.obj (op V.unop.2)))
private def coObj (M : PresheafOfModules.{r} ((Prod.sectR n C).op ⋙ A)) :
    PresheafOfModules.{r} A where
  obj := coValue A n M
  map {V W} a := ModuleCat.ofHom (X := coValue A n M V)
    (Y := (ModuleCat.restrictScalars (A.map a).hom).obj (coValue A n M W))
    { toFun := fun x h ↦ M.map a.unop.2.op (x ⟨h.down.trans (leOfHom a.unop.1)⟩)
      map_add' := by intros; funext h; exact map_add _ _ _
      map_smul' := by
        intro r x
        funext h
        change M.map a.unop.2.op
          ((A.map (hor n V (h.down.trans (leOfHom a.unop.1)))) r • x _) =
          (A.map (hor n W h.down)) ((A.map a) r) • M.map a.unop.2.op (x _)
        rw [M.map_smul]
        congr 1
        change (A.map (hor n V _) ≫ A.map ((Prod.sectR n C).map a.unop.2).op) r =
          (A.map a ≫ A.map (hor n W h.down)) r
        rw [← A.map_comp, ← A.map_comp]
        congr 2
        apply congrArg A.map
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext
        · apply Subsingleton.elim
        · simp [hor] }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.map_id]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (b.unop.2 ≫ a.unop.2).op (x _) =
      M.map b.unop.2.op (M.map a.unop.2.op (x _))
    rw [op_comp, M.map_comp_apply]
omit [UnivLE.{c, r}] [UnivLE.{v, r}] [UnivLE.{max c v, r}] in
private theorem sequence_isSheaf_of_slices {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type k)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

omit [UnivLE.{c, r}] in
private theorem abelianSheaf_iff (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{r}) :
    Presheaf.IsSheaf J P ↔ Presheaf.IsSheaf J (P ⋙ CategoryTheory.forget _) := by
  have : HasLimitsOfSize.{v, max v c} AddCommGrpCat.{r} :=
    hasLimitsOfSizeOfUnivLE.{r, r, v, max v c} AddCommGrpCat.{r}
  have : PreservesLimitsOfSize.{v, max v c} (CategoryTheory.forget AddCommGrpCat.{r}) :=
    preservesLimitsOfSize_of_univLE.{r, r, v, max v c}
      (CategoryTheory.forget AddCommGrpCat.{r})
  exact Presheaf.isSheaf_iff_isSheaf_comp J P (CategoryTheory.forget _)

private def coSheaf (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J)
      RingCat.{r}) (n : ℕ)
    (M : SheafOfModules.{r}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
        (coefficientSequenceTopology J)).obj A)) :
    SheafOfModules.{r} A where
  val := coObj A.obj n M.val
  isSheaf := by
    rw [abelianSheaf_iff.{c, v, r} _ _,
      isSheaf_iff_isSheaf_of_type]
    apply sequence_isSheaf_of_slices
    intro m U S hS x hx
    have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{r}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        ((abelianSheaf_iff.{c, v, r} J _).mp M.isSheaf)
    have hh (h : PLift (n ≤ m)) := hM S hS
      (fun {V} f hf ↦ x f hf h)
      (by
        intro V W Z a b f g hf hg hab
        exact congrFun (hx a b hf hg hab) h)
    choose a ha hu using hh
    refine ⟨fun h ↦ a h, ?_, ?_⟩
    · intro V f hf
      funext h
      exact ha h f hf
    · intro b hb
      funext h
      apply hu h (b h)
      intro V f hf
      exact congrFun (hb f hf) h

private def coFunctor (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ) :
    SheafOfModules.{r}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
        (coefficientSequenceTopology J)).obj A) ⥤ SheafOfModules.{r} A where
  obj := coSheaf J A n
  map {M N} f :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := coValue A.obj n M.val V)
          (Y := coValue A.obj n N.val V)
          { toFun := fun x h ↦ f.val.app (op V.unop.2) (x h)
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          exact PresheafOfModules.naturality_apply f.val a.unop.2.op (x _) } }

private def ev₀ (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ) :=
  SheafOfModules.pushforward.{r} (F := Prod.sectR n C)
    (𝟙 (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A))

private def coUnit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ) :
    𝟭 (SheafOfModules.{r} A) ⟶ ev₀ J A n ⋙ coFunctor J A n where
  app N :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := N.val.obj V)
          (Y := coValue A.obj n ((ev₀ J A n).obj N).val V)
          { toFun := fun x h ↦ N.val.map (hor n V h.down) x
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact N.val.map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          change N.val.map (hor n W h.down) (N.val.map a x) =
            N.val.map ((Prod.sectR n C).map a.unop.2).op (N.val.map (hor n V _) x)
          refine (N.val.map_comp_apply a (hor n W h.down) x).symm.trans
            ((N.val.congr_map_apply
              (f := a ≫ hor n W h.down)
              (g := hor n V (h.down.trans (leOfHom a.unop.1)) ≫
                ((Prod.sectR n C).map a.unop.2).op) ?_ x).trans
              (N.val.map_comp_apply (hor n V (h.down.trans (leOfHom a.unop.1)))
                ((Prod.sectR n C).map a.unop.2).op x))
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext
          · apply Subsingleton.elim
          · simp [hor] } }
  naturality {M N} f := by
    ext V x
    funext h
    exact (PresheafOfModules.naturality_apply f.val (hor n V h.down) x).symm

private def coCounit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ) :
    coFunctor J A n ⋙ ev₀ J A n ⟶ 𝟭 _ where
  app M :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom
          (X := ((ev₀ J A n).obj ((coFunctor J A n).obj M)).val.obj V)
          (Y := M.val.obj V)
          { toFun := fun x ↦ x ⟨le_refl n⟩
            map_add' := by intros; rfl
            map_smul' := by
              intro r x
              have hs : (r • x) ⟨le_refl n⟩ =
                  (A.obj.map (hor n (op (n, V.unop)) (le_refl n))) r •
                    (show M.val.obj V from x ⟨le_refl n⟩) := by
                rfl
              rw [hs]
              have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
                apply Quiver.Hom.unop_inj
                apply Prod.hom_ext
                · apply Subsingleton.elim
                · rfl
              rw [h, A.obj.map_id]
              rfl }
        naturality := by intros; rfl } }
  naturality := by intros; rfl

private def coAdj (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ) :
    ev₀ J A n ⊣ coFunctor J A n where
  unit := coUnit J A n
  counit := coCounit J A n
  left_triangle_components N := by
    ext V x
    change N.val.map (hor n (op (n, V.unop)) (le_refl n)) x = x
    have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · apply Subsingleton.elim
      · rfl
    rw [h, N.val.map_id]
    rfl
  right_triangle_components M := by
    ext V x
    funext h
    change M.val.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.val.map_id]
    rfl

omit [UnivLE.{c, r}] in
private theorem coMate_isIso
    {D : Type d} [Category.{w} D]
    [UnivLE.{d, r}] [UnivLE.{w, r}] [UnivLE.{max d w, r}]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{r}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
        (coefficientSequenceTopology J)).obj A ⟶
      (F.sheafPushforwardContinuous RingCat.{r} J K).obj
        (((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r} K
          (coefficientSequenceTopology K)).obj B))
    (d : SheafOfModules.pushforward.{r} φ ⋙ ev₀ J A n ≅
      ev₀ K B n ⋙ SheafOfModules.pushforward ψ) :
    IsIso (mateEquiv (coAdj K B n) (coAdj J A n) d.hom) := by
  let β : coFunctor K B n ⋙ SheafOfModules.pushforward φ ⟶
      SheafOfModules.pushforward ψ ⋙ coFunctor J A n :=
    (mateEquiv (coAdj K B n) (coAdj J A n) d.hom)
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  let T := SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj
  have ht : IsIso (T.map (β.app M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let : Unique (PLift (n ≤ n)) :=
      { default := ⟨le_refl n⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }
    let e := Equiv.funUnique (PLift (n ≤ n)) (M.val.obj (op (F.obj V.unop.2)))
    let g := (d.hom.app ((coFunctor K B n).obj M)).val.app (op V.unop.2)
    let γ := e ∘ g ∘ e.symm
    have hg : Function.Bijective g := by
      let S := ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
        (coefficientSequenceTopology J)).obj A
      let Q := SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj
      exact ConcreteCategory.bijective_of_isIso
        ((Q.map (d.hom.app ((coFunctor K B n).obj M))).app (op V.unop.2))
    have hγ : Function.Bijective γ :=
      e.bijective.comp (hg.comp e.symm.bijective)
    have hf : (fun x ↦ (T.map (β.app M)).app V x) =
        Pi.map (fun (_ : PLift (n ≤ V.unop.1)) ↦ γ) := by
      funext x h
      change (((SheafOfModules.pushforward ψ).map ((coAdj K B n).counit.app M)).val.app
        (op V.unop.2)
        ((d.hom.app ((coFunctor K B n).obj M)).val.app (op V.unop.2)
          (((SheafOfModules.pushforward φ).obj ((coFunctor K B n).obj M)).val.map
            (hor n V h.down) x))) = γ (x h)
      have hx :
          (((SheafOfModules.pushforward φ).obj ((coFunctor K B n).obj M)).val.map
            (hor n V h.down) x) = (fun (_ : PLift (n ≤ n)) ↦ x h) := by
        funext hn
        change M.val.map (F.map (𝟙 V.unop.2)).op (x _) = x h
        rw [F.map_id, op_id, M.val.map_id]
        rfl
      rw [hx]
      rfl
    change Function.Bijective (fun x ↦ (T.map (β.app M)).app V x)
    rw [hf]
    exact Function.Bijective.piMap (fun _ ↦ hγ)
  let := ht
  exact isIso_of_reflects_iso (β.app M) T

private def coFor (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ)
    (S : Sheaf J RingCat.{r})
    (h : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S) :
    SheafOfModules.{r} S ⥤ SheafOfModules.{r} A := by
  subst S
  exact coFunctor J A n

private def coForAdj (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r}) (n : ℕ)
    (S : Sheaf J RingCat.{r})
    (h : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S) :
    SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom h.symm) ⊣
      coFor J A n S h := by
  subst S
  exact coAdj J A n

omit [UnivLE.{c, r}] in
private theorem coForMate_isIso
    {D : Type d} [Category.{w} D]
    [UnivLE.{d, r}] [UnivLE.{w, r}] [UnivLE.{max d w, r}]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{r}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{r}) (T : Sheaf K RingCat.{r})
    (hA : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S)
    (hB : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj T)
    (d : SheafOfModules.pushforward.{r} φ ⋙
        SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hA.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n D) (eqToHom hB.symm) ⋙
        SheafOfModules.pushforward ψ) :
    IsIso (mateEquiv (coForAdj K B n T hB) (coForAdj J A n S hA) d.hom) := by
  subst S
  subst T
  exact coMate_isIso J K F A B n φ ψ d

omit [UnivLE.{c, r}] [UnivLE.{v, r}] [UnivLE.{max c v, r}] in
private theorem inverseMate_isIso_of_iterated
    {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (d : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    [IsIso (mateEquiv adj₄ adj₃ d)] :
    IsIso ((mateEquiv adj₁ adj₂).symm d) := by
  let α := (mateEquiv adj₁ adj₂).symm d
  have h := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α) := by
    rw [← h]
    infer_instance
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α

/-- Inverse image commutes with finite evaluation for any direct-image comparison
isomorphism. The sites and coefficient universes are independent.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-sequence-module-pullback-evaluation).

Proof: evaluation at n has a right adjoint. At (m,U) its sections are M(U) if
n ≤ m and zero otherwise, with scalars restricted by the horizontal ring map.
The unit is horizontal restriction and the counit is evaluation at n. The mate
of the direct-image comparison under these coextension adjunctions acts pointwise
by its invertible n-th section map, hence is invertible. Taking iterated mates identifies
this mate with the conjugate of the inverse-image evaluation map. Conjugation
reflects invertibility, giving the asserted isomorphism. -/
theorem sequenceModulePullbackEvaluation_isIso
    {D : Type d} [Category.{w} D]
    [UnivLE.{d, r}] [UnivLE.{w, r}] [UnivLE.{max d w, r}]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{r}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{r}) (T : Sheaf K RingCat.{r})
    (hA : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r} J
      (coefficientSequenceTopology J)).obj A = S)
    (hB : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj T)
    (L : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B)
    (Ln : SheafOfModules.{r} S ⥤ SheafOfModules.{r} T)
    (adj : L ⊣ SheafOfModules.pushforward φ)
    (adjn : Ln ⊣ SheafOfModules.pushforward ψ)
    (d : SheafOfModules.pushforward.{r} φ ⋙
        SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hA.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n D) (eqToHom hB.symm) ⋙
        SheafOfModules.pushforward ψ) :
    IsIso ((mateEquiv adj adjn).symm d.hom) := by
  have : IsIso (mateEquiv (coForAdj K B n T hB) (coForAdj J A n S hA) d.hom) :=
    coForMate_isIso J K F A B n φ S T hA hB ψ d
  exact inverseMate_isIso_of_iterated adj adjn
    (coForAdj J A n S hA) (coForAdj K B n T hB) d.hom

end WeilConjectures.SequenceModuleEvaluation
