/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionFunctors

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralProjectiveLineAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralTateLineConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralTensorInverseImage
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Integral affine-space purity from the projective-line adjunction

Source: current blueprint, sk-thm-int-restriction-line.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-affine-purity-induction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
-- Avoid repeated expansion of the large private categorical helper signatures.
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

local notation "Λ₀" => Profinite.padicIntegersRingObj ℓ E.val

attribute [local irreducible] Adjunction.ofNatIsoLeft Adjunction.ofNatIsoRight
  Adjunction.comp Adjunction.restrictFullyFaithful

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar lowerStar upperStarLowerStarAdjunction

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] spIntegralTwist
  InternalAbelianSheafModule.comparison_tensorIso
  InternalAbelianSheafModule.comparison_unitIso

private noncomputable def transportAdjunction
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (e : F ≅ F') (r : G ≅ G') : F' ⊣ G' :=
  (a.ofNatIsoLeft e).ofNatIsoRight r

private noncomputable def composeAdjunctions
    {C D B : Type*} [Category C] [Category D] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ B} {I : B ⥤ D}
    {L : C ⥤ B} {R : B ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (e : F ⋙ H ≅ L) (r : I ⋙ G ≅ R) : L ⊣ R :=
  transportAdjunction (a.comp b) e r

attribute [local irreducible] transportAdjunction composeAdjunctions

@[instance_reducible]
private noncomputable instance pullCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (IntegralCompactSupport.pull Λ₀ f).CommShift ℤ :=
  unboundedLocalizingPullbackCommShift _ f

@[instance_reducible]
private noncomputable instance tensorCommShift (X : Scheme.{u})
    (T : IntegralCompactSupport.Ambient Λ₀ X) :
    (tensorRight T).CommShift ℤ :=
  DerivedCategory.commShiftTensorRight _ T

private theorem localizing_preimage
    {C D : Type v} [Category.{w} C] [Category.{w'} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (P : ObjectProperty D) (hP : IsLocalizingSubcategory P) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsLeftAdjoint] :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG h
  let := hG
  have hcol : P (colimit (G ⋙ F)) := hP.prop_colimit (G ⋙ F) inferInstance (fun i ↦ h i)
  exact P.prop_of_iso (preservesColimitIso F G).symm hcol

attribute [local irreducible] tateLine

private theorem twistedPull_constructible (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ)
    (hline : boundedConstructible (condensedRingObj
      Λ₀ X)
        ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))))
    (K : IntegralCompactSupport.Ambient Λ₀ Y)
    (hK : constantModelBoundedConstructible Λ₀ Y K) :
    constantModelBoundedConstructible Λ₀ X
      ((pullTwistShift ℓ E f d).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have eY := (adicConstructibilityPredicateComparison ℓ Y Λ
    (IsEllAdicCoefficient.integral E.val)).2
  have eX := (adicConstructibilityPredicateComparison ℓ X Λ
    (IsEllAdicCoefficient.integral E.val)).2
  have hK' := (congrFun eY K).mpr hK
  apply (congrFun eX _).mp
  have : IsNoetherian X := ⟨⟩
  have : (boundedConstructible (condensedRingObj Λ X)).IsTriangulated :=
    isTriangulated_boundedConstructible_padicIntegersRingObj X ℓ E.val
  have ht := integralTensorInverseImage ℓ E k f
  have h := ht.2.1 _ _ (ht.1 K hK').1 hline
  exact (boundedConstructible (condensedRingObj Λ X)).le_shift _ _ h

private theorem twistedPull_localizing {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hbc : ∀ K, constantModelBoundedConstructible
      Λ₀ Y K →
      constantModelBoundedConstructible Λ₀ X
        ((pullTwistShift ℓ E f d).obj K)) :
    ∀ K, IntegralCompactSupport.localizing Λ₀ Y K →
      IntegralCompactSupport.localizing Λ₀ X
        ((pullTwistShift ℓ E f d).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let T := (DerivedCategory.singleFunctor C 0).obj (tateLine ℓ E X (d : ℤ))
  let F := IntegralCompactSupport.pull Λ f ⋙ (curriedTensor (DerivedCategory C)).flip.obj T
  let P := IntegralCompactSupport.localizing Λ X
  have hP := (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X)).2.2.2.1
  let : P.IsTriangulated := hP.1
  let : P.IsClosedUnderIsomorphisms := hP.2.1
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  let : (IntegralCompactSupport.pull Λ f).IsTriangulated :=
    Functor.isTriangulated_of_iso e
  let : (IntegralCompactSupport.pull Λ f).IsLeftAdjoint :=
    (derivedUpperStarLowerStarAdjunction Λ f).isLeftAdjoint
  let : BraidedCategory (DerivedCategory C) := (DerivedCategory.nonempty_braidedCategory C).some
  let : F.CommShift ℤ := by dsimp only [F]; infer_instance
  let : ((curriedTensor (DerivedCategory C)).flip.obj T).IsTriangulated :=
    DerivedCategory.isTriangulated_tensorRight C T
  have : F.IsTriangulated := by dsimp only [F]; infer_instance
  have : F.IsLeftAdjoint := by dsimp [F]; infer_instance
  intro K hK
  have hF : P ((shiftFunctor _ (2 * (d : ℤ))).obj (F.obj K)) := by
    apply P.le_shift
    apply hK (P.inverseImage F)
    · exact localizing_preimage P hP F
    · intro L hL
      have h := (localizingClosure_exists Λ X
        (constantModelBoundedConstructible Λ X)).2.2.2.2.1 _ (hbc L hL)
      exact (P.prop_shift_iff_of_isStableUnderShift (F.obj L) (2 * (d : ℤ))).mp h
  exact hF

private noncomputable def liftIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun A ↦ P.isoMk (e.app A)) (by
    intro A B m
    apply ObjectProperty.hom_ext
    exact e.hom.naturality m)

attribute [local irreducible] liftIso

private noncomputable def restrictAdjunction
    {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (hF : ∀ K, P K → Q (F.obj K)) (hG : ∀ K, Q K → P (G.obj K)) :
    Q.lift (P.ι ⋙ F) (fun K ↦ hF K.obj K.property) ⊣
      P.lift (Q.ι ⋙ G) (fun K ↦ hG K.obj K.property) :=
  a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι P)
    (ObjectProperty.fullyFaithfulι Q)
    (Q.liftCompιIso (P.ι ⋙ F) _).symm (P.liftCompιIso (Q.ι ⋙ G) _).symm

private theorem equivalence_exact {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) : exactFunctor C D e.functor :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

private theorem exact_of_inverse {C : Type*} [Category C]
    (F G : C ⥤ C) (a : F ⋙ G ≅ 𝟭 C) (b : G ⋙ F ≅ 𝟭 C) :
    exactFunctor C C F :=
  equivalence_exact (CategoryTheory.Equivalence.mk F G a.symm b)

attribute [local irreducible] restrictAdjunction

private theorem composite_geometry {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    IsSeparated (f ≫ g) ∧ LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g) :=
  ⟨MorphismProperty.comp_mem (@IsSeparated) f g inferInstance inferInstance,
    locallyOfFiniteType_comp f g, quasiCompact_comp f g⟩

private noncomputable def space (k : Type u) [Field k] (T : Scheme.{u})
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    IntegralCompactSupport.Spaces k :=
  ⟨Over.mk (T ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (T ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (T ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (T ↘ Spec (.of k)))⟩⟩

private noncomputable def properImageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] :
    IntegralCompactSupport.image Λ₀
        (Compactification.ofIsProper f) ≅
      IntegralCompactSupport.push Λ₀ f :=
  Functor.isoWhiskerRight
      (derivedOpenImmersionLowerShriekId Λ₀ X) _ ≪≫
    Functor.leftUnitor _

attribute [local irreducible] properImageIso

private theorem properPush_localizing (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    ∀ K, IntegralCompactSupport.localizing Λ₀ X K →
      IntegralCompactSupport.localizing Λ₀ Y
        ((IntegralCompactSupport.push Λ₀ f).obj K) := by
  let fs : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let c : Compactification.QuasiCompactObjects f :=
    ⟨Compactification.ofIsProper f, quasiCompact_of_isIso (𝟙 X)⟩
  obtain ⟨pres, _, _, _⟩ := IntegralCompactSupport.integralLocalizingCompactSupport ℓ E k
  have hP := (localizingClosure_exists Λ₀ Y
    (constantModelBoundedConstructible Λ₀ Y)).2.2.2.1
  let : (IntegralCompactSupport.localizing Λ₀ Y).IsClosedUnderIsomorphisms := hP.2.1
  intro K hK
  exact (IntegralCompactSupport.localizing Λ₀ Y).prop_of_iso
    ((properImageIso ℓ E f).app K) (pres.maps_localizing (f := fs) c K hK)

@[instance_reducible]
private noncomputable def residueUnits (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    ∀ x : X, Invertible (ℓ : X.residueField x) := by
  have hl : (ℓ : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ ℓ)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz)
  intro x
  let φ : k →+* X.residueField x :=
    (X ↘ Spec (.of k)).residueFieldAlgebraMap x
  exact (show IsUnit (ℓ : X.residueField x) by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl).map φ).invertible

attribute [local irreducible] residueUnits

open CategoryTheory.MonoidalCategory

attribute [local semireducible] tateLine

private noncomputable abbrev sectionEquiv (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj Λ₀ X)

private noncomputable def inverseUnitIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (e : C ≌ D) (t : e.functor.obj (𝟙_ C) ≅ 𝟙_ D) :
    e.inverse.obj (𝟙_ D) ≅ 𝟙_ C :=
  e.functor.preimageIso (e.counitIso.app (𝟙_ D) ≪≫ t.symm)

private noncomputable def inverseTensorIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (e : C ≌ D) (t : ∀ M N, e.functor.obj (M ⊗ N) ≅
      e.functor.obj M ⊗ e.functor.obj N) (A B : D) :
    e.inverse.obj (A ⊗ B) ≅ e.inverse.obj A ⊗ e.inverse.obj B :=
  e.functor.preimageIso (e.counitIso.app (A ⊗ B) ≪≫
    tensorIso (e.counitIso.app A).symm (e.counitIso.app B).symm ≪≫
      (t (e.inverse.obj A) (e.inverse.obj B)).symm)

attribute [local irreducible] inverseUnitIso inverseTensorIso

private noncomputable def tateLine_zero (X : Scheme.{u}) :
    tateLine ℓ E X 0 ≅ 𝟙_ _ := by
  have e₀ := InternalAbelianSheafModule.comparison_unitIso
    (Scheme.ProEt.topology X)
    (condensedRingObj Λ₀ X)
  exact inverseUnitIso (sectionEquiv ℓ E X) e₀

private noncomputable def tateLine_one (X : Scheme.{u}) :
    tateLine ℓ E X 1 ≅ spIntegralTwist X ℓ E :=
  ((sectionEquiv ℓ E X).unitIso.app (spIntegralTwist X ℓ E)).symm

private noncomputable def tateLine_succ (X : Scheme.{u}) (n : ℕ) :
    tateLine ℓ E X ((n + 1 : ℕ) : ℤ) ≅
      tateLine ℓ E X (n : ℤ) ⊗ tateLine ℓ E X 1 := by
  cases n with
  | zero =>
    exact (λ_ _).symm ≪≫ tensorIso (tateLine_zero ℓ E X).symm (Iso.refl _)
  | succ n =>
    let e := sectionEquiv ℓ E X
    let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (condensedRingObj Λ₀ X)
    let L := e.functor.obj (spIntegralTwist X ℓ E)
    let A := WeilConjectures.coefficientTwistPower X L (n + 1)
    have t := InternalAbelianSheafModule.comparison_tensorIso
      (Scheme.ProEt.topology X)
      (condensedRingObj Λ₀ X)
    exact e.inverse.mapIso ((SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R L).app A) ≪≫
      inverseTensorIso e t A L

private noncomputable def pull_tateLine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    (upperStar Λ₀ f).obj
        (tateLine ℓ E Y (n : ℤ)) ≅ tateLine ℓ E X (n : ℤ) := by
  induction n with
  | zero =>
    exact (upperStar _ f).mapIso (tateLine_zero ℓ E Y) ≪≫
      (Functor.Monoidal.εIso (upperStar _ f)).symm ≪≫ (tateLine_zero ℓ E X).symm
  | succ n ih =>
    have : IsIso (spIntegralComparison f ℓ E) := nativeIntegralComparison_isIso f ℓ E
    let e := Classical.choose (ordinaryIntegralComparison_iso_exists f ℓ E)
    have e₁ : (upperStar Λ₀ f).obj
        (tateLine ℓ E Y 1) ≅ tateLine ℓ E X 1 :=
      (upperStar _ f).mapIso (tateLine_one ℓ E Y) ≪≫ e ≪≫ (tateLine_one ℓ E X).symm
    exact (upperStar _ f).mapIso (tateLine_succ ℓ E Y n) ≪≫
      (Functor.Monoidal.μIso (upperStar _ f) _ _).symm ≪≫ tensorIso ih e₁ ≪≫
      (tateLine_succ ℓ E X n).symm

attribute [local irreducible] tateLine tateLine_zero tateLine_one tateLine_succ pull_tateLine

private theorem tateLine_flat (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ObjectProperty.flat (tateLine ℓ E X 1) := by
  let L := (sectionEquiv ℓ E X).functor.obj (spIntegralTwist X ℓ E)
  have : L.IsFiniteLocallyFreeOfRank 1 := (spTwists_locallyFree X ℓ E).1
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
    (condensedRingObj Λ₀ X)
  have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) L := by
    obtain ⟨a⟩ := (WeilConjectures.signedLineTensor_equivalence X R L 1).2
    obtain ⟨b⟩ := (WeilConjectures.signedLineTensor_equivalence X R L (-1)).2
    let G := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (WeilConjectures.coefficientTwistLine X L (-1))
    let H := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L
    have b' : G ⋙ H ≅ 𝟭 _ := by
      simpa only [G, H, WeilConjectures.coefficientTwistLine,
        WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower,
        neg_neg] using b
    change exactFunctor _ _ H
    exact exact_of_inverse H G a b'
  exact ObjectProperty.prop_of_iso ObjectProperty.flat (tateLine_one ℓ E X).symm
    ((InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology X) (condensedRingObj Λ₀ X) (spIntegralTwist X ℓ E)).mpr hflat)

private noncomputable def single_tensor
    {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w'} C] [Abelian.HasFunctorialFlatResolution C]
    (M N : C) (hN : ObjectProperty.flat N) :
    (DerivedCategory.singleFunctor C 0).obj M ⊗
        (DerivedCategory.singleFunctor C 0).obj N ≅
      (DerivedCategory.singleFunctor C 0).obj (M ⊗ N) := by
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj N
  have hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    (CochainComplex.kFlat_single_obj_iff_flat N 0).mpr hN
  exact tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app N) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatRight _ P hP ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) N).app _) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (tensorRight N) (.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app (M ⊗ N)).symm

attribute [local irreducible] single_tensor

private noncomputable abbrev twistObject (X : Scheme.{u}) (n : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (n : ℤ))

private noncomputable def twistObject_succ (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (n : ℕ) :
    twistObject ℓ E X n ⊗ twistObject ℓ E X 1 ≅ twistObject ℓ E X (n + 1) :=
  single_tensor _ _ (tateLine_flat ℓ E X) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateLine_succ ℓ E X n).symm

private noncomputable def pull_twistObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    (IntegralCompactSupport.pull Λ₀ f).obj
      (twistObject ℓ E Y n) ≅ twistObject ℓ E X n :=
  (leftDerivedUpperStarIsoMapDerivedCategory _ f).app _ ≪≫
    ((upperStar _ f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pull_tateLine ℓ E f n)

attribute [local irreducible] twistObject_succ pull_twistObject

private noncomputable def tensorShiftZero
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [HasShift D ℤ]
    (F : C ⥤ D) (A : D) (e : A ≅ 𝟙_ D) :
    F ⋙ tensorRight A ⋙ shiftFunctor D (0 : ℤ) ≅ F :=
  Functor.isoWhiskerLeft F
    (Functor.isoWhiskerRight ((curriedTensor D).flip.mapIso e) _ ≪≫
      Functor.isoWhiskerLeft _ (shiftFunctorZero D ℤ) ≪≫
      Functor.rightUnitor _ ≪≫ rightUnitorNatIso D) ≪≫ Functor.rightUnitor F

attribute [local irreducible] tensorShiftZero

private noncomputable def pullTwistShift_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullTwistShift ℓ E f 0 ≅
      IntegralCompactSupport.pull Λ₀ f := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ₀ X)
  let e : twistObject ℓ E X 0 ≅ 𝟙_ (DerivedCategory C) :=
    (DerivedCategory.singleFunctor C 0).mapIso (tateLine_zero ℓ E X) ≪≫
      DerivedCategory.singleFunctorObjUnitIso C
  exact tensorShiftZero (IntegralCompactSupport.pull
    Λ₀ f) (twistObject ℓ E X 0) e

private noncomputable def tensorShiftPull
    {C D B : Type*} [Category C] [Category D] [Category B]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.Monoidal] [F.CommShift ℤ] (G : B ⥤ C)
    (A : C) (T : D) (e : F.obj A ≅ T) (n : ℤ) :
    (G ⋙ tensorRight A ⋙ shiftFunctor C n) ⋙ F ≅
      (G ⋙ F) ⋙ tensorRight T ⋙ shiftFunctor D n := by
  have t : tensorRight A ⋙ F ≅ F ⋙ tensorRight T :=
    (Functor.Monoidal.commTensorRight F A).symm ≪≫
      Functor.isoWhiskerLeft F ((curriedTensor D).flip.mapIso e)
  exact Functor.associator G _ F ≪≫
    Functor.isoWhiskerLeft G (Functor.associator _ _ F) ≪≫
    Functor.isoWhiskerLeft G (Functor.isoWhiskerLeft _ (F.commShiftIso n)) ≪≫
    Functor.isoWhiskerLeft G (Functor.associator _ F _).symm ≪≫
    Functor.isoWhiskerLeft G (Functor.isoWhiskerRight t _) ≪≫
    Functor.isoWhiskerLeft G (Functor.associator F _ _) ≪≫
    (Functor.associator G F _).symm

private noncomputable def tensorShiftTensor
    {C B : Type*} [Category C] [Category B] [MonoidalCategory C] [HasShift C ℤ]
    (F : B ⥤ C) (A T U : C) [(tensorRight T).CommShift ℤ]
    (e : A ⊗ T ≅ U) (n m t : ℤ) (h : n + m = t) :
    (F ⋙ tensorRight A ⋙ shiftFunctor C n) ⋙
        tensorRight T ⋙ shiftFunctor C m ≅
      F ⋙ tensorRight U ⋙ shiftFunctor C t := by
  have e' : tensorRight A ⋙ tensorRight T ≅ tensorRight U :=
    (tensorRightTensor A T).symm ≪≫ (curriedTensor C).flip.mapIso e
  exact Functor.associator F _ _ ≪≫
    Functor.isoWhiskerLeft F (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((tensorRight T).commShiftIso n) _ ≪≫
          Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft F (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight e' _) ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft _ (shiftFunctorAdd' C n m t h).symm)

attribute [local irreducible] tensorShiftPull tensorShiftTensor

private noncomputable def pullTwistShift_pull {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    pullTwistShift ℓ E g n ⋙
        IntegralCompactSupport.pull Λ₀ f ≅
      pullTwistShift ℓ E (f ≫ g) n := by
  exact tensorShiftPull (IntegralCompactSupport.pull
      Λ₀ f)
      (IntegralCompactSupport.pull Λ₀ g)
      (twistObject ℓ E Y n) (twistObject ℓ E X n) (pull_twistObject ℓ E f n) _ ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp
      Λ₀ f g).symm _

private noncomputable def pullTwistShift_succ {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    pullTwistShift ℓ E g n ⋙ pullTwistShift ℓ E f 1 ≅
      pullTwistShift ℓ E (f ≫ g) (n + 1) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X)
  let T := twistObject ℓ E X 1
  let B := tensorRight T ⋙ shiftFunctor (DerivedCategory C) (2 : ℤ)
  exact (Functor.associator (pullTwistShift ℓ E g n) (IntegralCompactSupport.pull Λ₀ f)
      B).symm ≪≫
    Functor.isoWhiskerRight (pullTwistShift_pull ℓ E f g n) B ≪≫
    tensorShiftTensor (IntegralCompactSupport.pull Λ₀ (f ≫ g))
      (twistObject ℓ E X n) T (twistObject ℓ E X (n + 1))
      (twistObject_succ ℓ E X n) (2 * (n : ℤ)) 2 (2 * ((n + 1 : ℕ) : ℤ)) (by omega)

attribute [local irreducible] pullTwistShift
  pullTwistShift_zero pullTwistShift_pull pullTwistShift_succ

open IntegralCompactSupport

private def lowerCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (μ : Compositions Λ k)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f)
    (d : Compactification.BoundaryCompactification g)
    (e : Compactification.BoundaryCompactification (f ≫ g))
    (hf : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K))
    (hg : ∀ K, localizing Λ Y K → localizing Λ Z ((image Λ d.obj.obj).obj K))
    (hgf : ∀ K, localizing Λ X K → localizing Λ Z ((image Λ e.obj.obj).obj K)) :
    IntegralCompactSupport.lowerShriek Λ c.obj.obj hf ⋙
      IntegralCompactSupport.lowerShriek Λ d.obj.obj hg ≅
      IntegralCompactSupport.lowerShriek Λ e.obj.obj hgf := by
  let f' : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let g' : space k Y ⟶ space k Z := ObjectProperty.homMk (g.asOver (Spec (.of k)))
  let e0 := μ f' g' c.obj d.obj e.obj
  refine NatIso.ofComponents (fun K ↦ (localizing Λ Z).isoMk (e0.app K)) ?_
  intro K L m
  apply ObjectProperty.hom_ext
  exact e0.hom.naturality m

attribute [local irreducible] lowerCompIso

private theorem image_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (h : Preservation Λ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f) :
    ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K) := by
  exact h.maps_localizing (X := space k X) (Y := space k Y)
    (f := ObjectProperty.homMk (f.asOver (Spec (.of k)))) c.obj

private theorem pull_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {h : Preservation Λ k} {φ : Comparisons Λ k}
    {μ : Compositions Λ k} (hc : Coherence Λ k h φ μ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K) := by
  exact hc.localizing_pull (X := space k X) (Y := space k Y)
    (ObjectProperty.homMk (f.asOver (Spec (.of k))))

private noncomputable def pullLift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, localizing Λ Y K → localizing Λ X ((pull Λ f).obj K)) :
    (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory :=
  (localizing Λ X).lift ((localizing Λ Y).ι ⋙ pull Λ f)
    (fun K ↦ h K.obj K.property)

private theorem twisted_preserves (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) :
    ∀ K, localizing Λ₀ Y K →
      localizing Λ₀ X
        ((pullTwistShift ℓ E f d).obj K) := by
  let : ∀ x : X, Invertible (ℓ : X.residueField x) := residueUnits ℓ k X
  exact twistedPull_localizing ℓ E f d
    (twistedPull_constructible ℓ E k f d (integralTateLine_constructible ℓ E X _))

private def Purity {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ (hp : ∀ K, localizing Λ₀ Y K →
      localizing Λ₀ X
        ((pullTwistShift ℓ E f d).obj K))
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing Λ₀ X K →
      localizing Λ₀ Y
        ((image Λ₀ c.obj.obj).obj K)),
    Nonempty (IntegralCompactSupport.lowerShriek
      Λ₀ c.obj.obj h ⊣
      restrictedPull ℓ E f d hp)

attribute [local irreducible] Purity

private theorem affineLine_purity (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] :
    Purity ℓ E (AffineSpace PUnit.{u + 1} T ↘ T) 1 := by
  unfold Purity
  let A := AffineSpace PUnit.{u + 1} T
  let P := ProjectiveLine T
  let j : A ⟶ P := ProjectiveLine.affineChart T
  let q : P ⟶ T := P ↘ T
  let p : A ⟶ T := A ↘ T
  have hA := composite_geometry p (T ↘ Spec (.of k))
  let : IsSeparated (A ↘ Spec (.of k)) := hA.1
  let : LocallyOfFiniteType (A ↘ Spec (.of k)) := hA.2.1
  let : QuasiCompact (A ↘ Spec (.of k)) := hA.2.2
  have hP := composite_geometry q (T ↘ Spec (.of k))
  let : IsSeparated (P ↘ Spec (.of k)) := hP.1
  let : LocallyOfFiniteType (P ↘ Spec (.of k)) := hP.2.1
  let : QuasiCompact (P ↘ Spec (.of k)) := hP.2.2
  let : j.IsOver (Spec (.of k)) := ⟨by
    change j ≫ q ≫ T ↘ Spec (.of k) = p ≫ T ↘ Spec (.of k)
    rw [← Category.assoc, ProjectiveLine.affineChart_over]⟩
  let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace
    (A ↘ Spec (.of k))
  let : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated
    (P ↘ Spec (.of k))
  let : QuasiCompact j := quasiCompact_of_compactSpace j
  let : ∀ x : A, Invertible (ℓ : A.residueField x) := residueUnits ℓ k A
  let : ∀ x : P, Invertible (ℓ : P.residueField x) := residueUnits ℓ k P
  obtain ⟨pres, φ, μ, hc⟩ := integralLocalizingCompactSupport ℓ E k
  let cj : Compactification.QuasiCompactObjects j :=
    ⟨Compactification.ofIsOpenImmersion j, inferInstanceAs (QuasiCompact j)⟩
  let js : space k A ⟶ space k P := ObjectProperty.homMk (j.asOver (Spec (.of k)))
  have eid : push Λ₀ (𝟙 P) ≅ 𝟭 _ :=
    Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarId Λ₀ P) ≪≫
      Functor.rightDerivedFunctorIdIso _
  have ej : image Λ₀ cj.obj ≅ extend Λ₀ j :=
    Functor.isoWhiskerLeft (extend Λ₀ j) eid ≪≫ Functor.rightUnitor _
  have hP := (localizingClosure_exists Λ₀ P
    (constantModelBoundedConstructible Λ₀ P)).2.2.2.1
  let : (localizing Λ₀ P).IsClosedUnderIsomorphisms := hP.2.1
  have hj : ∀ K, localizing Λ₀ A K → localizing Λ₀ P ((extend Λ₀ j).obj K) := by
    intro K hK
    exact (localizing Λ₀ P).prop_of_iso (ej.app K) (pres.maps_localizing (f := js) cj K hK)
  have hjp := pull_localizing Λ₀ k hc j
  let J := (localizing Λ₀ P).lift ((localizing Λ₀ A).ι ⋙ extend Λ₀ j)
    (fun K ↦ hj K.obj K.property)
  let R := pullLift Λ₀ j hjp
  have adjj := restrictAdjunction (localizing Λ₀ A) (localizing Λ₀ P)
    (F := extend Λ₀ j) (G := pull Λ₀ j) (openAdjunction Λ₀ j) hj hjp
  have hq := twisted_preserves ℓ E k q 1
  have hr := properPush_localizing ℓ E k q
  obtain ⟨adjq⟩ := integralProjectiveLine_adjunction ℓ E k T hq hr
  intro hp c h
  let cp : Compactification.QuasiCompactObjects p :=
    ⟨affineTraceLineCompactification T, inferInstanceAs (QuasiCompact j)⟩
  let fs : space k A ⟶ space k T := ObjectProperty.homMk (p.asOver (Spec (.of k)))
  have el : IntegralCompactSupport.lowerShriek Λ₀ c.obj.obj h ≅ J ⋙ restrictedPush ℓ E q hr :=
    liftIso (localizing Λ₀ T) (φ fs c.obj cp)
  have ep : pullTwistShift ℓ E (j ≫ q) 1 ≅ pullTwistShift ℓ E p 1 :=
    eqToIso (congrArg (fun t : A ⟶ T ↦ pullTwistShift ℓ E t 1)
      (ProjectiveLine.affineChart_over T))
  have er : restrictedPull ℓ E q 1 hq ⋙ R ≅ restrictedPull ℓ E p 1 hp :=
    liftIso (localizing Λ₀ A)
      (Functor.associator (localizing Λ₀ T).ι (pullTwistShift ℓ E q 1) (pull Λ₀ j) ≪≫
        Functor.isoWhiskerLeft (localizing Λ₀ T).ι (pullTwistShift_pull ℓ E j q 1 ≪≫ ep))
  exact ⟨composeAdjunctions adjj adjq el.symm er⟩

private theorem purity_comp (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (n m t : ℕ) (hf : Purity ℓ E f n) (hg : Purity ℓ E g m)
    (er : pullTwistShift ℓ E g m ⋙ pullTwistShift ℓ E f n ≅
      pullTwistShift ℓ E (f ≫ g) t) : Purity ℓ E (f ≫ g) t := by
  unfold Purity at hf hg ⊢
  obtain ⟨pres, φ, μ, hc⟩ := integralLocalizingCompactSupport ℓ E k
  let c := AlgebraicGeometry.compactificationOverField k f
  let d := AlgebraicGeometry.compactificationOverField k g
  have hf' := image_localizing Λ₀ k pres f c
  have hg' := image_localizing Λ₀ k pres g d
  have hfp := twisted_preserves ℓ E k f n
  have hgp := twisted_preserves ℓ E k g m
  obtain ⟨af⟩ := hf hfp c hf'
  obtain ⟨ag⟩ := hg hgp d hg'
  intro hp e h
  have el := lowerCompIso Λ₀ k μ f g c d e hf' hg' h
  have er' : restrictedPull ℓ E g m hgp ⋙ restrictedPull ℓ E f n hfp ≅
      restrictedPull ℓ E (f ≫ g) t hp :=
    liftIso (localizing Λ₀ X) (Functor.isoWhiskerLeft (localizing Λ₀ Z).ι er)
  exact ⟨composeAdjunctions af ag el er'⟩

private theorem iso_purity (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))] : Purity ℓ E e.hom 0 := by
  unfold Purity
  obtain ⟨pres, φ, μ, hc⟩ := integralLocalizingCompactSupport ℓ E k
  have hpf := pull_localizing Λ₀ k hc e.hom
  let R := pullLift Λ₀ e.hom hpf
  let cp : Compactification.QuasiCompactObjects e.hom :=
    ⟨Compactification.ofIsOpenImmersion e.hom, quasiCompact_of_isIso e.hom⟩
  let fs : space k X ⟶ space k Y :=
    ObjectProperty.homMk (e.hom.asOver (Spec (.of k)))
  have hcp := pres.maps_localizing (f := fs) cp
  have eid : push Λ₀ (𝟙 Y) ≅ 𝟭 _ :=
    Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarId Λ₀ Y) ≪≫
      Functor.rightDerivedFunctorIdIso _
  have ei : image Λ₀ cp.obj ≅ extend Λ₀ e.hom :=
    Functor.isoWhiskerLeft (extend Λ₀ e.hom) eid ≪≫ Functor.rightUnitor _
  have a := (openAdjunction Λ₀ e.hom).ofNatIsoLeft ei.symm
  have ar := restrictAdjunction (localizing Λ₀ X) (localizing Λ₀ Y)
    (F := image Λ₀ cp.obj) (G := pull Λ₀ e.hom) a hcp hpf
  intro hp c h
  have el : IntegralCompactSupport.lowerShriek Λ₀ c.obj.obj h ≅
      IntegralCompactSupport.lowerShriek Λ₀ cp.obj hcp :=
    liftIso (localizing Λ₀ Y) (φ fs c.obj cp)
  have er : restrictedPull ℓ E e.hom 0 hp ≅ R :=
    liftIso (localizing Λ₀ X) (Functor.isoWhiskerLeft (localizing Λ₀ Y).ι
      (pullTwistShift_zero ℓ E e.hom))
  exact ⟨transportAdjunction ar el.symm er.symm⟩

private theorem tower_purity (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (d : ℕ) :
    Purity ℓ E (affineTraceProjection Y d) d := by
  induction d with
  | zero =>
    let : (Iso.refl Y).hom.IsOver (Spec (.of k)) := ⟨Category.id_comp _⟩
    exact iso_purity ℓ E k (Iso.refl Y)
  | succ d ih =>
    let T := affineTraceTower Y d
    let g := affineTraceProjection Y d
    let : T.Over (Spec (.of k)) := ⟨g ≫ Y ↘ Spec (.of k)⟩
    let : g.IsOver (Spec (.of k)) := ⟨rfl⟩
    have hT := composite_geometry g (Y ↘ Spec (.of k))
    let : IsSeparated (T ↘ Spec (.of k)) := hT.1
    let : LocallyOfFiniteType (T ↘ Spec (.of k)) := hT.2.1
    let : QuasiCompact (T ↘ Spec (.of k)) := hT.2.2
    let A := AffineSpace PUnit.{u + 1} T
    let f : A ⟶ T := A ↘ T
    have hA := composite_geometry f (T ↘ Spec (.of k))
    let : IsSeparated (A ↘ Spec (.of k)) := hA.1
    let : LocallyOfFiniteType (A ↘ Spec (.of k)) := hA.2.1
    let : QuasiCompact (A ↘ Spec (.of k)) := hA.2.2
    let : ∀ x : A, Invertible (ℓ : A.residueField x) := residueUnits ℓ k A
    let : ∀ x : T, Invertible (ℓ : T.residueField x) := residueUnits ℓ k T
    exact purity_comp ℓ E k f g 1 d (d + 1) (affineLine_purity ℓ E k T) ih
      (pullTwistShift_succ ℓ E f g d)

/-- The standard affine chart and the coordinate tower turn projective-line
purity into the compact-support adjunction for every affine dimension.

Source: sk-thm-int-restriction-line.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-affine-purity-induction).

Proof: for A1_T -> T use its standard open immersion into P1_T. This open
immersion is quasi-compact because its source is quasi-compact and its target
is quasi-separated. Extension by zero preserves Loc(Dbc). Restrict its adjunction
with open pullback, then compose it with
the projective-line adjunction. Cartesian twists identify the right adjoint
with the prescribed pullback, degree-one twist and shift two. Compactification
independence transports the left adjoint to any chosen compactification.
For dimension zero, the affine projection is an isomorphism; the zero tensor
power and zero shift reduce the assertion to its identity adjunction. At the
successor use the coordinate isomorphism A^(d+1)_Y = A1_(A^d_Y), compose the
line adjunction with the induction adjunction, and use pullback composition,
Cartesian twist comparison, tensor-power addition and shift addition. Both
shifts are even. Compact-support composition and compactification independence
identify the composed left adjoint with the displayed one. This proves the
assertion uniformly over every standing base, including the empty base. -/
theorem integralAffinePurity_induction
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (d : ℕ)
    (hp : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y)
        ((pullTwistShift ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d).obj K))
    (c : Compactification.BoundaryCompactification
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
    (h : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (AffineSpace (ULift.{u} (Fin d)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
          c.obj.obj).obj K)) :
    Nonempty (IntegralCompactSupport.lowerShriek
      (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣
        restrictedPull ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d hp) := by
  let T := affineTraceTower Y d
  let g := affineTraceProjection Y d
  let A := AffineSpace (ULift.{u} (Fin d)) Y
  let p : A ⟶ Y := A ↘ Y
  let : T.Over (Spec (.of k)) := ⟨g ≫ Y ↘ Spec (.of k)⟩
  let : g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hT := composite_geometry g (Y ↘ Spec (.of k))
  let : IsSeparated (T ↘ Spec (.of k)) := hT.1
  let : LocallyOfFiniteType (T ↘ Spec (.of k)) := hT.2.1
  let : QuasiCompact (T ↘ Spec (.of k)) := hT.2.2
  have hA := composite_geometry p (Y ↘ Spec (.of k))
  let : IsSeparated (A ↘ Spec (.of k)) := hA.1
  let : LocallyOfFiniteType (A ↘ Spec (.of k)) := hA.2.1
  let : QuasiCompact (A ↘ Spec (.of k)) := hA.2.2
  let e : A ≅ T := (affineTraceAffineSpaceIso Y d).symm
  have he : e.inv ≫ p = g := AffineSpace.homOfVector_over _ _
  have he' : e.hom ≫ g = p := by rw [← he]; simp
  let : e.hom.IsOver (Spec (.of k)) := ⟨by
    change e.hom ≫ (g ≫ Y ↘ Spec (.of k)) = p ≫ Y ↘ Spec (.of k)
    rw [← Category.assoc, he']⟩
  let : ∀ x : A, Invertible (ℓ : A.residueField x) := residueUnits ℓ k A
  let : ∀ x : T, Invertible (ℓ : T.residueField x) := residueUnits ℓ k T
  have er : pullTwistShift ℓ E g d ⋙ pullTwistShift ℓ E e.hom 0 ≅
      pullTwistShift ℓ E (e.hom ≫ g) d :=
    Functor.isoWhiskerLeft _ (pullTwistShift_zero ℓ E e.hom) ≪≫
      pullTwistShift_pull ℓ E e.hom g d
  have ht := purity_comp ℓ E k e.hom g 0 d d
    (iso_purity ℓ E k e) (tower_purity ℓ E k Y d) er
  rw [he'] at ht
  unfold Purity at ht
  exact ht hp c h

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
