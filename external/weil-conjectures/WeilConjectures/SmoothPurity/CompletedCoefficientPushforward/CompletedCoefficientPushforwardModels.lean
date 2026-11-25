/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
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
/-!
# Models for completed-coefficient direct image and its strict quotient tower

(blueprint: def-pur-completed-pushforward-models).

Source: Stacks Tags 0D6E, 0A07 and 099N (1),(4); blueprint fix-prop-adjunctions, Step 1
(blueprint: lem-pur-completed-coefficient-pushforward-comparison).

All sites retain their object and morphism universes. The auxiliary records retain
universal derived units and representative normalizations; their existence is a conclusion.
The constructions and signatures are the existing completed-coefficient comparison interface.
They are re-exported by CompletedCoefficientPushforwardComparison; the extraction permits
its independent proof lemmas to use the interface without an import cycle.

## Main definitions and statement

- `RightImage`, `ExactImage`, and `Square`: derived models and their normalized comparisons.
- `SiteData`: exact scalar restrictions, strict coefficient systems, and derived tower limits.
- `ComparisonData`: coefficient coherence, strict diagrams, and complete reconstruction.
- `ComparisonData.completeComparison`: the comparison restricted to complete source objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward

section DerivedModels
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) [F.PreservesZeroMorphisms]

/-- A total right derived image with its universal unit and K-injective computation.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure RightImage where
  functor : DerivedCategory A ⥤ DerivedCategory B
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

/-- Exact coefficient restriction is computed termwise on all complexes.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure ExactImage where
  functor : DerivedCategory A ⥤ DerivedCategory B
  factors : DerivedCategory.Q ⋙ functor ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
/-- The unit of exact coefficient restriction, fixed before localization.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure ExactIdentity (G : A ⥤ A) [G.PreservesZeroMorphisms] (DG : ExactImage G) where
  ordinary : G ≅ 𝟭 A
  comparison : DG.functor ≅ 𝟭 (DerivedCategory A)
  normalization : ∀ K : CochainComplex A ℤ,
    comparison.hom.app (DerivedCategory.Q.obj K) = DG.factors.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)
end DerivedModels

section Squares
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type z} [Category.{zv} D] [Abelian D] [HasDerivedCategory.{d} D]
  (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [V.PreservesZeroMorphisms]
  (RF : RightImage F) (RG : RightImage G) (DU : ExactImage U) (DV : ExactImage V)

/-- The comparison of the two factorizations of a ringed direct image, including its
normalization on the common underived composite. Source: Stacks Tag 0D6E
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure Square where
  ordinary : F ⋙ V ≅ U ⋙ G
  comparison : RF.functor ⋙ DV.functor ≅ DU.functor ⋙ RG.functor
  normalization : ∀ K : CochainComplex A ℤ,
    DV.functor.map (RF.unit.app K) ≫ comparison.hom.app (DerivedCategory.Q.obj K) ≫
        RG.functor.map (DU.factors.hom.app K) =
      DV.factors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K) ≫
        RG.unit.app ((U.mapHomologicalComplex (.up ℤ)).obj K)
/-- Composition of termwise exact restrictions, normalized before localization.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure ExactComposition (H : A ⥤ D) [H.PreservesZeroMorphisms]
    (DH : ExactImage H) (E₁ : ExactImage F) (E₂ : ExactImage V) where
  ordinary : F ⋙ V ≅ H
  comparison : E₁.functor ⋙ E₂.functor ≅ DH.functor
  normalization : ∀ K : CochainComplex A ℤ,
    comparison.hom.app (DerivedCategory.Q.obj K) ≫ DH.factors.hom.app K =
      E₂.functor.map (E₁.factors.hom.app K) ≫
        E₂.factors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)
end Squares

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded module category at any ring sheaf on the original small site.
Source: Stacks Tag 03DA (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev Mod (W : Scheme.{t}) (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)} B

/-- A natural map of module sheaves is the identity on the underlying sections.
The heterogeneous equality just forgets the possibly different scalar actions.
Source: Stacks Tag 0D6E
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
def IsSectionwiseIdentity (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    {C : Type c} [Category.{cv} C] {F G : C ⥤ Mod W B} (η : F ⟶ G) : Prop :=
  ∀ (M : C) (U : W.ProEtᵒᵖ) (x : (F.obj M).val.obj U),
    HEq ((η.app M).val.app U x) x

/-- Mathlib's abelian structure, with both sheafification universes specified.
Source: Stacks Tag 03DA
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
instance (priority := 20000) modAbelian (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) : Abelian (Mod W B) :=
  { @SheafOfModules.instAbelian.{max u (t + 1), t, max u (t + 1), t + 1}
      W.ProEt inferInstance (ProEt.topology W) B
      (integralCoefficientAbSheafify.{t, u} W)
      (integralCoefficientAbLocallyBijective.{t, u} W) with
    toPreadditive := inferInstance }

/-- The existing standard localization, selected uniformly for ordinary derived models.
Source: Stacks Tag 05RU
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
instance (priority := 10000) hasDerived {A : Type a} [Category.{av} A] [Abelian A] :
    HasDerivedCategory.{max a av} A := HasDerivedCategory.standard A

/-- Precomposition on ring sheaves in the coefficient universe, with no universe equality.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev ringPush {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

/-- The constant structural map, obtained by sheafification of constant sections.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
def constantPush {X Y : Scheme.{t}} (f : X ⟶ Y) (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
    (ringPush.{t, u} f).obj ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t
      + 1)})).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)) :=
  let B := (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)
  let h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    (B.obj ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  ⟨Functor.whiskerRight h.hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- Module direct image is the actual sectionwise pushforward along its structural map.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev push {X Y : Scheme.{t}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    {S : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    (c : R ⟶ (ringPush.{t, u} f).obj S) : Mod X S ⥤ Mod Y R :=
  SheafOfModules.pushforward.{max u (t + 1)} c

/-- The coefficient-ring action in the existing strict coefficient-system category.
Source: Zheng Construction 4.1 (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev systemRing := ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)

/-- The generator of the principal ideal defining the existing strict coefficient systems.
Source: Zheng Construction 4.1 (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev systemUniformizer : systemRing.{t, u} l E :=
  ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- The existing strict semilinear coefficient systems, without a normalization condition.
Source: Zheng Construction 4.1 (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev Systems (W : Scheme.{t}) :=
  SheafOfModules.CoefficientSystem.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
    (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E)

/-- The actual completed coefficient ring, abbreviated only for the comparison signature.
Source: Stacks Tag 03CO (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev R (W : Scheme.{t}) := completedIntegralCoefficientSheafUnrestricted l E W

/-- The actual constant coefficient ring.
Source: Stacks Tag 03CO (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev A (W : Scheme.{t}) := integralConstantRingOfUniverses l E W

/-- The actual finite coefficient ring at exponent n+1.
Source: Stacks Tag 03CO (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev N (W : Scheme.{t}) (n : ℕ) := integralCoefficientSheaf l E W n

/-- The exact finite-level ring maps are the already recorded tower maps.
The explicit endpoints keep the sequence implementation out of downstream types.
Source: blueprint order 1455 (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
def quotientMap (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m) : N l E W m ⟶ N l E W n :=
  (integralCoefficientSheafSystem l E W).map (homOfLE h).op

/-- The actual limit projection at exponent n+1.
Source: Stacks Tag 03CO (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev projection (W : Scheme.{t}) (n : ℕ) : R l E W ⟶ N l E W n :=
  limit.π (integralCoefficientSheafSystem l E W) (op n)

/-- The existing quotient sheaf used by strict systems, with commutativity forgotten.
Source: Zheng Construction 4.1 (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev modelRing (W : Scheme.{t}) (n : ℕ) :
    Sheaf (ProEt.topology W) RingCat.{max u (t + 1)} :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (SheafOfModules.coefficientQuotientSheaf.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
        (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) n)

/-- Transport from the existing strict-system finite coefficient presentation along
its ring isomorphism; this is restriction along the inverse, with unchanged sections.
Source: Stacks Tag 03DA (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev model (W : Scheme.{t}) (n : ℕ) (e : modelRing l E W n ≅ N l E W n) :=
  SheafOfModules.restrictScalars.{max u (t + 1)} e.inv

/-- The ordinary limit of strict completed-module towers, with its category fixed before
instance synthesis. Source: Stacks Tag 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev ordinaryTowerLimit (W : Scheme.{t}) :
    (ℕᵒᵖ ⥤ Mod W (R l E W)) ⥤ Mod W (R l E W) := lim

set_option genSizeOf false in
set_option genInjectivity false in
/-- Exact coefficient restrictions and their quotient composition laws.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure SiteCoefficientData (W : Scheme.{t}) where
  U : ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)}
    (integralConstantToCompletionOfUniverses l E W))
  V : ∀ n, ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n))
  restriction : ∀ {m n : ℕ} (h : n ≤ m), ExactImage
    (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W h))
  finiteIso : ∀ n, modelRing l E W n ≅ N l E W n
  finiteIso_generator : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (a : systemRing.{t, u} l E),
    ((finiteIso n).hom.hom.app U)
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (systemRing.{t, u} l E ⧸
            (Ideal.span ({systemUniformizer.{t, u} l E} : Set (systemRing.{t, u} l E))) ^
              (n + 1))))).app U (Ideal.Quotient.mk _ a)) =
      (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))
  restrictionComposition : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    ExactComposition
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W hmn))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W hkm))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W (hmn.trans hkm)))
      (restriction (hmn.trans hkm)) (restriction hmn) (restriction hkm)
  restrictionComposition_identity : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    IsSectionwiseIdentity W (N l E W k) (restrictionComposition hkm hmn).ordinary.hom
  restrictionIdentity : ∀ n, ExactIdentity
    (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W (le_refl n)))
    (restriction (le_refl n))
  restrictionIdentity_sections : ∀ n,
    IsSectionwiseIdentity W (N l E W n) (restrictionIdentity n).ordinary.hom
  projectionComposition : ∀ {m n : ℕ} (h : n ≤ m),
    ExactComposition
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W h))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W m))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n))
      (V n) (restriction h) (V m)
  projectionComposition_identity : ∀ {m n : ℕ} (h : n ≤ m),
    IsSectionwiseIdentity W (R l E W) (projectionComposition h).ordinary.hom

set_option genSizeOf false in
set_option genInjectivity false in
/-- The actual restriction of semilinear coefficient systems to strict completed-module towers.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure SystemRestrictionData (W : Scheme.{t}) extends SiteCoefficientData l E W where
  systemRestriction : Systems l E W ⥤ (ℕᵒᵖ ⥤ Mod W (R l E W))
  [systemRestrictionAdditive : systemRestriction.Additive]
  systemEvaluation : ∀ n, systemRestriction ⋙ (evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n) ≅
    SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E W n (finiteIso n) ⋙
          SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n)
  systemEvaluation_identity : ∀ n,
    IsSectionwiseIdentity W (R l E W) (systemEvaluation n).hom
  systemTransition : ∀ (M : Systems l E W) (n : ℕ) (U : W.ProEtᵒᵖ),
    HEq (fun x ↦ (((systemRestriction.obj M).map (homOfLE (Nat.le_succ n)).op).val.app U) x)
      (fun x ↦ ((M.transition n).val.app U) x)
  systemMap : ∀ (M M' : Systems l E W) (h : M ⟶ M') (n : ℕ) (U : W.ProEtᵒᵖ),
    HEq (fun x ↦ (((systemRestriction.map h).app (op n)).val.app U) x)
      (fun x ↦ ((h.app n).val.app U) x)
  systemFactors : ExactImage systemRestriction

attribute [instance] SystemRestrictionData.systemRestrictionAdditive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The ordinary strict-tower limit and its normalized total derived functor.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure SiteLimitData (W : Scheme.{t}) where
  [limitAdditive : (ordinaryTowerLimit l E W).Additive]
  limit : RightImage (ordinaryTowerLimit l E W)
  evaluation : ∀ n, ExactImage ((CategoryTheory.evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n))
  limitProjection : ∀ n, limit.functor ⟶ (evaluation n).functor
  limitProjection_normalization : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ) n,
    limit.unit.app M ≫ (limitProjection n).app (DerivedCategory.Q.obj M) ≫
        (evaluation n).factors.hom.app M =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lim.π (op n) : (ordinaryTowerLimit l E W) ⟶
          (CategoryTheory.evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n)) (.up ℤ)).app M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Site-side coefficient restrictions, strict systems, and total derived limits.
All functors retain their original universal or termwise normalizations.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure SiteData (W : Scheme.{t}) extends
    SystemRestrictionData l E W, SiteLimitData l E W where

variable {X Y : Scheme.{t}} (f : X ⟶ Y)

/-- The canonical finite structural map is the constant-section map for the finite ring.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev finiteStructure (n : ℕ) :=
  constantPush.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The constant integral structural map is the constant-section map for the integer ring.
Source: Stacks Tag 0D6E (blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
abbrev constantStructure :=
  constantPush.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The augmentation of one strict flat reduction tower: in every degree it is x↦x⊗1.
This is a property of an actual map into the ordinary limit, not an arbitrary lift in
an unenhanced triangulated category. Source: Bhatt--Scholze Definition 3.5.2; Stacks 03EK
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
def IsReductionAugmentation (W : Scheme.{t})
    (P : CochainComplex (Mod W (R l E W)) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E W P)
    (a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex
      (.up ℤ)).obj C) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U),
    ((a.f i ≫ limit.π (C.X i) (op n) ≫ (e.hom.app (op n)).f i).val.app U) x =
      unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x

set_option genSizeOf false in
set_option genInjectivity false in
/-- The actual direct images and the normalized constant and finite coefficient squares.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure CoefficientImageData where
  source : SiteData l E X
  target : SiteData l E Y
  structureMap : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)
  structureProjection : ∀ n, structureMap ≫ (ringPush.{t, u} f).map (projection l E X n) =
    projection l E Y n ≫ finiteStructure l E f n
  [completedAdditive : (push f structureMap).Additive]
  [constantAdditive : (push f (constantStructure l E f)).Additive]
  [finiteAdditive : ∀ n, (push f (finiteStructure l E f n)).Additive]
  completedImage : RightImage (push f structureMap)
  constantImage : RightImage (push f (constantStructure l E f))
  finiteImage : ∀ n, RightImage (push f (finiteStructure l E f n))
  constantSquare : Square (push f structureMap) (push f (constantStructure l E f))
    (SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E X))
    (SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E Y))
    completedImage constantImage source.U target.U
  finiteSquare : ∀ n, Square (push f (finiteStructure l E f n)) (push f structureMap)
    (SheafOfModules.restrictScalars (projection l E X n))
    (SheafOfModules.restrictScalars (projection l E Y n))
    (finiteImage n) completedImage (source.V n) (target.V n)
  quotientSquare : ∀ {m n : ℕ} (h : n ≤ m),
    Square (push f (finiteStructure l E f n)) (push f (finiteStructure l E f m))
      (SheafOfModules.restrictScalars (quotientMap l E X h))
      (SheafOfModules.restrictScalars (quotientMap l E Y h))
      (finiteImage n) (finiteImage m) (source.restriction h) (target.restriction h)

attribute [instance] CoefficientImageData.completedAdditive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The section identities, restriction coherence, and completion-projection compatibility.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure CoefficientComparisonData extends CoefficientImageData l E f where
  constantOrdinary_identity :
    IsSectionwiseIdentity Y (A l E Y) constantSquare.ordinary.hom
  finiteOrdinary_identity : ∀ n,
    IsSectionwiseIdentity Y (R l E Y) (finiteSquare n).ordinary.hom
  quotientOrdinary_identity : ∀ {m n : ℕ} (h : n ≤ m),
    IsSectionwiseIdentity Y (N l E Y m) (quotientSquare h).ordinary.hom
  quotientIdentity : ∀ n (K : DerivedCategory (Mod X (N l E X n))),
    (quotientSquare (le_refl n)).comparison.hom.app K ≫
        (finiteImage n).functor.map ((source.restrictionIdentity n).comparison.hom.app K) =
      (target.restrictionIdentity n).comparison.hom.app ((finiteImage n).functor.obj K)
  quotientCoherence : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m)
    (K : DerivedCategory (Mod X (N l E X n))),
    (quotientSquare (hmn.trans hkm)).comparison.hom.app K ≫
        (finiteImage k).functor.map ((source.restrictionComposition hkm hmn).comparison.inv.app K) =
      (target.restrictionComposition hkm hmn).comparison.inv.app ((finiteImage n).functor.obj K) ≫
        (target.restriction hkm).functor.map ((quotientSquare hmn).comparison.hom.app K) ≫
        (quotientSquare hkm).comparison.hom.app ((source.restriction hmn).functor.obj K)
  projectionCoherence : ∀ {m n : ℕ} (h : n ≤ m) (K : DerivedCategory (Mod X (N l E X n))),
    (finiteSquare n).comparison.hom.app K =
      (target.projectionComposition h).comparison.inv.app ((finiteImage n).functor.obj K) ≫
        (target.V m).functor.map ((quotientSquare h).comparison.hom.app K) ≫
        (finiteSquare m).comparison.hom.app ((source.restriction h).functor.obj K) ≫
        completedImage.functor.map ((source.projectionComposition h).comparison.hom.app K)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The comparison on derived strict coefficient diagrams and its normalized limit projections.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure DiagramComparisonData extends CoefficientComparisonData l E f where
  systemPush : Systems l E X ⥤ Systems l E Y
  [systemPushAdditive : systemPush.Additive]
  systemPushEvaluation : ∀ n,
    systemPush ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology Y)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E Y n (target.finiteIso n) ≅
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E X n (source.finiteIso n) ⋙ push f (finiteStructure l E f n)
  systemPushEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (N l E Y n) (systemPushEvaluation n).hom
  systemImage : RightImage systemPush
  towerImage : RightImage ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap))
  diagramSquare : Square systemPush
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap))
    source.systemRestriction target.systemRestriction systemImage towerImage
    source.systemFactors target.systemFactors
  diagramOrdinary_identity : ∀ (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((target.systemRestriction.obj (systemPush.obj M)).obj (op n)).val.obj U),
      HEq ((((diagramSquare.ordinary.hom.app M).app (op n)).val.app U) x) x
  towerEvaluation : ∀ n, Square
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap)) (push f structureMap)
    ((evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n))
    ((evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n))
    towerImage completedImage (source.evaluation n) (target.evaluation n)
  towerEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (R l E Y) (towerEvaluation n).ordinary.hom
  ordinaryLimit :
    (ordinaryTowerLimit l E X) ⋙ push f structureMap ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap) ⋙
        (ordinaryTowerLimit l E Y)
  ordinaryLimit_projections : ∀ M, ordinaryLimit.hom.app M = limit.post M (push f structureMap)
  limitComparison : source.limit.functor ⋙ completedImage.functor ≅
    towerImage.functor ⋙ target.limit.functor
  limitNormalization : ∀ C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ,
    completedImage.unit.app
        (((ordinaryTowerLimit l E X).mapHomologicalComplex
          (.up ℤ)).obj C) ≫
      completedImage.functor.map (source.limit.unit.app C) ≫
        limitComparison.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinaryLimit (.up ℤ)).hom.app C) ≫
        target.limit.unit.app
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap)).mapHomologicalComplex
            (.up ℤ)).obj C) ≫ target.limit.functor.map (towerImage.unit.app C)
  limitProjection : ∀ (M : DerivedCategory (ℕᵒᵖ ⥤ Mod X (R l E X))) n,
    limitComparison.hom.app M ≫ (target.limitProjection n).app (towerImage.functor.obj M) ≫
        (towerEvaluation n).comparison.hom.app M =
      completedImage.functor.map ((source.limitProjection n).app M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- All coefficient comparisons, strict derived diagrams, and complete reconstruction.
The inherited records retain every canonical map and normalization.
Source: Stacks Tags 0D6E and 0A07
(blueprint: lem-pur-completed-coefficient-pushforward-comparison). -/
structure ComparisonData extends DiagramComparisonData l E f where
  preservesComplete : ∀ K : DerivedCategory (Mod X (R l E X)),
    IsDerivedCompleteUnrestricted l E X K →
      IsDerivedCompleteUnrestricted l E Y (completedImage.functor.obj K)
  strictReductionExists : ∀ P : CochainComplex (Mod X (R l E X)) ℤ,
    ∃ C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ,
      Nonempty (C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P)
  reductionAugmentation : ∀ (P : CochainComplex (Mod X (R l E X)) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P),
    ∃! a : P ⟶ ((ordinaryTowerLimit l E X).mapHomologicalComplex
      (.up ℤ)).obj C, IsReductionAugmentation l E X P C e a
  reconstruction : ∀ (K : DerivedCategory (Mod X (R l E X)))
    (P : CochainComplex (Mod X (R l E X)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} X.ProEt
      inferInstance (ProEt.topology X) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} X)
      (integralCoefficientAbSheafify.{t, u} X).isRightAdjoint
      (completedIntegralCommRingSheafUnrestricted l E X) (P.X i)) →
    ∀ (r : DerivedCategory.Q.obj P ≅ K)
      (C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ)
      (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P)
      (a : P ⟶ ((ordinaryTowerLimit l E X).mapHomologicalComplex
        (.up ℤ)).obj C),
    IsReductionAugmentation l E X P C e a → IsDerivedCompleteUnrestricted l E X K →
      IsIso (completedImage.functor.map (r.inv ≫ DerivedCategory.Q.map a ≫ source.limit.unit.app C)
        ≫
        limitComparison.hom.app (DerivedCategory.Q.obj C))

end WeilConjectures.CompletedCoefficientPushforward
