/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing
import all WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperDirectSums
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import all WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperCohomologicalBounds
import all WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartConstructibleCohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedCoproducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-!
# Proper direct image on localizing categories

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-proper-image-localizing/sk-prop-proper-image-localizing-proper.md and its proof
(blueprint: proposition-proper-direct-image-extension-zero--1).

The coefficient list uses bundled ring objects, so membership identifies both the
underlying condensed abelian sheaf and its multiplication. The two auxiliary predicates
spell out the hypotheses and conclusion of this node, using the recorded ambient
module-object derived category and localizing closure. Coproduct indices have universe
`u + 2`, exactly the indexing universe in the recorded closure of this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj

private theorem localizingClosure_isLocalizing
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : IsLocalizingSubcategory (localizingClosure S) := by
  let L := localizingClosure S
  have hIso : L.IsClosedUnderIsomorphisms := ⟨by
    intro K K' e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)⟩
  let := hIso
  have hZero : L.ContainsZero := ⟨⟨0, isZero_zero C, by
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero⟩⟩
  have hShift : L.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro K hK P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)⟩⟩
  have hTri : L.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃ P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS))
  refine ⟨?_, hIso, ?_⟩
  · exact
      { toContainsZero := hZero
        toIsStableUnderShift := hShift
        toIsTriangulatedClosed₂ := hTri }
  · intro I F hF h
    change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → P (colimit F)
    intro P hP hS
    exact hP.2.2 F hF (fun i ↦ h i P hP hS)

private theorem localizingClosure_map
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hS : ∀ K, S K → T (F.obj K))
    (hF : ∀ (I : Type v) (G : Discrete I ⥤ (localizingClosure S).FullSubcategory),
      PreservesColimit (G ⋙ (localizingClosure S).ι) F) :
    ∀ K, localizingClosure S K → localizingClosure T (F.obj K) := by
  let L := localizingClosure S
  let M := localizingClosure T
  have hL := localizingClosure_isLocalizing S
  have hM := localizingClosure_isLocalizing T
  let := hL.1
  let := hL.2.1
  let := hM.1
  let := hM.2.1
  let P := L ⊓ M.inverseImage F
  have hP : IsLocalizingSubcategory P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG h
    let := hG
    have hLG : L (colimit G) := hL.2.2 G hG (fun i ↦ (h i).1)
    refine ⟨hLG, ?_⟩
    let G' := L.lift G (fun i ↦ (h i.as).1)
    have : PreservesColimit G F := hF I G'
    have hMG : M (colimit (G ⋙ F)) :=
      hM.prop_colimit (G ⋙ F) inferInstance (fun i ↦ (h i).2)
    exact M.prop_of_iso (preservesColimitIso F G).symm hMG
  intro K hK
  exact (hK P hP (fun K hK ↦ ⟨fun Q hQ hSQ ↦ hSQ K hK,
    fun Q hQ hTQ ↦ hTQ _ (hS K hK)⟩)).2

-- Upgrade the small canonical cofan comparison on a class to every existing sum.
private theorem preservesColimit_on_class
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D]
    (S : ObjectProperty C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hsmall : ∀ (J : Type v) (K : J → C), (∀ j, S (K j)) →
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))
    {I : Type w} (G : Discrete I ⥤ C) (hG : ∀ i, S (G.obj ⟨i⟩)) :
    PreservesColimit G F := by
  let K : I → C := fun i ↦ G.obj ⟨i⟩
  have : PreservesColimit (Discrete.functor K) F := by
    constructor
    intro c hc
    exact AlgebraicGeometry.ProEtale.preservesCofanOnClass S F hsmall K hG c hc
  exact preservesColimit_of_iso_diagram (K₁ := Discrete.functor K) (K₂ := G)
    F (Discrete.natIsoFunctor (F := G)).symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two hypotheses in the proper localizing-image statement: preservation of
bounded constructible finite-Tor objects and of ambient sums of localizing objects.
Source: blueprint proposition-proper-direct-image-extension-zero--1, first paragraph
(blueprint: proposition-proper-direct-image-extension-zero--1). -/
def ProperLocalizingHypotheses
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  (∀ K : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ Y ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
        ((lowerStar Λ p).rightDerivedFunctor.obj K.obj)) ∧
  ∀ (I : Type (u + 2)) (F : Discrete I ⥤ (localizingClosureProEtale Λ X).FullSubcategory),
    PreservesColimit (F ⋙ (localizingClosureProEtale Λ X).ι)
      (lowerStar Λ p).rightDerivedFunctor

/-- The sum-preservation hypothesis of `ProperLocalizingHypotheses` for a sum indexed by the
universe of the morphisms: lift the index along `ULift`, the index categories being equivalent. -/
theorem preservesColimit_of_properLocalizingHypotheses
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ProperLocalizingHypotheses Λ p) (I : Type (u + 1))
    (G : Discrete I ⥤ (localizingClosureProEtale Λ X).FullSubcategory) :
    PreservesColimit (G ⋙ (localizingClosureProEtale Λ X).ι)
      (lowerStar Λ p).rightDerivedFunctor := by
  have : PreservesColimit ((Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)).functor ⋙
      (G ⋙ (localizingClosureProEtale Λ X).ι)) (lowerStar Λ p).rightDerivedFunctor :=
    h.2 (ULift.{u + 2} I) ((Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)).functor ⋙ G)
  exact preservesColimit_of_preservesColimit_ulift _ _

/-- The canonical restriction of the total derived pushforward is triangulated
and preserves every small coproduct. The subcategory structures are the induced
ones from the ambient derived categories, and the functor is the standard lift of
inclusion followed by the total derived pushforward, with its induced shift structure.
Source: blueprint proposition-proper-direct-image-extension-zero--1, first paragraph
(blueprint: proposition-proper-direct-image-extension-zero--1). -/
def ProperLocalizingRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X) ∧
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y) ∧
  ∀ [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X)]
    [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y)],
  ∃ h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K.obj),
    (ObjectProperty.lift (localizingClosureProEtale Λ Y)
      ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor)
      h).IsTriangulated ∧
    ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
      (ObjectProperty.lift (localizingClosureProEtale Λ Y)
        ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor) h)

/-- Proper direct image restricts to an exact, sum-preserving functor on the
localizing categories, provided it preserves the generators and ambient sums of
localizing objects. The coefficient list is exactly the admissible list, with the
finite ring discrete, finite subfield E, and finite-subextension condensed Qbar.

Source: blueprint proposition-proper-direct-image-extension-zero--1, first paragraph and first
proof paragraph (blueprint: proposition-proper-direct-image-extension-zero--1).

Proof: lowerStar is additive, so its total right derived functor is triangulated
(lem-pc-right-derived-functor-triangulated). Inside the source localizing closure,
take the objects whose image belongs to the target localizing closure. Exactness
makes this subcategory replete and triangulated. The first hypothesis puts all
Dctf generators in it. For a family in it, the second hypothesis identifies the
image of its ambient sum with the sum of its images, so this subcategory is
closed under sums. Minimality of definition-localizing-subcategory makes it the entire
source closure. ObjectProperty.isTriangulated_lift gives exactness of the lift
(situation-conventions). Fullness and closure under sums
identify subcategory coproducts with ambient coproducts, giving preservation of
sums by that same lift. Only sums of localizing objects were used. -/
theorem proper_image_localizing_proper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] :
    ProperLocalizingHypotheses Λ.X p → ProperLocalizingRestriction Λ.X p := by
  intro h
  let S := constantModelBoundedConstructible Λ.X X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let T := constantModelBoundedConstructible Λ.X Y ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosure S
  let M := localizingClosure T
  let F := (lowerStar Λ.X p).rightDerivedFunctor
  have hL := localizingClosure_isLocalizing S
  have hM := localizingClosure_isLocalizing T
  refine ⟨hL.1, hM.1, ?_⟩
  intro instL instM
  let := hL.2.1
  let := hM.2.1
  have hmap : ∀ K : L.FullSubcategory, M (F.obj K.obj) := fun K ↦
    localizingClosure_map S T F (fun K hK ↦ h.1 ⟨K, hK⟩)
      (preservesColimit_of_properLocalizingHypotheses Λ.X p h) K.obj K.property
  refine ⟨hmap, inferInstance, ?_⟩
  let C := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C :=
    fun I ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete I)
  have : HasCoproducts.{u + 1}
      (DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X))) := derived_hasCoproducts
  have hι (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) L.ι := by
    have hclosed : L.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} I)) :=
      .mk' (by
        rintro K ⟨G, hG⟩
        exact hL.prop_colimit G inferInstance (fun i ↦ hG ⟨i⟩))
    let := hclosed
    have : L.IsClosedUnderColimitsOfShape (Discrete I) :=
      L.isClosedUnderColimitsOfShape_discrete_of_ulift I
    let := createsColimitsOfShapeFullSubcategoryInclusion (Discrete I) L
    infer_instance
  intro I
  have : PreservesColimitsOfShape (Discrete I) L.ι :=
    Functor.preservesColimitsOfShape_discrete_of_small L.ι hι I
  constructor
  intro G
  have : PreservesColimit (G ⋙ L.ι) F := h.2 I G
  have : PreservesColimit G (L.ι ⋙ F) := inferInstance
  have : PreservesColimit G (M.lift (L.ι ⋙ F) hmap ⋙ M.ι) :=
    preservesColimit_of_natIso G (M.liftCompιIso (L.ι ⋙ F) hmap).symm
  exact preservesColimit_of_reflects_of_preserves (M.lift (L.ι ⋙ F) hmap) M.ι

attribute [local irreducible] Functor.rightDerivedFunctor upperStarFromPoint

private theorem properHypotheses_of_bc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hX : (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ X)
    (hY : (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ Y)
    (hgen : ∀ K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K))
    (hsum : ∀ (I : Type (u + 1))
      (K : I → DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))),
      (∀ i, localizingClosure (constantModelBoundedConstructible Λ X) (K i)) →
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((lowerStar Λ p).rightDerivedFunctor.mapCocone c))) :
    ProperLocalizingHypotheses Λ p := by
  constructor
  · intro K
    exact (congrFun hY _).mpr (hgen K.obj K.property.1)
  · intro I G
    apply preservesColimit_on_class
      (localizingClosure (constantModelBoundedConstructible Λ X)) _ hsum
    intro i
    have h := (G.obj ⟨i⟩).property
    change localizingClosure (_ ⊓ _) _ at h
    rwa [hX] at h

private theorem properHypotheses_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ProperLocalizingHypotheses Λ' p) : ProperLocalizingHypotheses Λ p := by
  let e₀ : Λ ≅ Λ' := (Mon.forget _).mapIso e
  have : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsMonHom e₀.inv := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso e₀.inv := inferInstance
  let H (Z : Scheme.{u}) :
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z) :=
    Mod.comap (coefficientMap e₀.inv Z)
  have hEq (Z : Scheme.{u}) : (H Z).IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap e₀.inv Z)).functor.IsEquivalence
  have hflat (Z : Scheme.{u}) : (H Z).PreservesFlat :=
    Functor.preservesFlat_of_isEquivalence (H Z)
  have hext (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e₀.inv Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let HX := (H X).mapDerivedCategory
  let HY := (H Y).mapDerivedCategory
  have hDEq (Z : Scheme.{u}) : (H Z).mapDerivedCategory.IsEquivalence := inferInstance
  have hcols (Z : Scheme.{u}) :
      PreservesColimitsOfSize.{u + 2, u + 2} (H Z).mapDerivedCategory := inferInstance
  have hHX {I : Type (u + 2)} (K : Discrete I ⥤ _) : PreservesColimit K HX :=
    (hcols X).preservesColimitsOfShape.preservesColimit
  have hcolsSmall (Z : Scheme.{u}) :
      PreservesColimitsOfSize.{u + 1, u + 1} (H Z).mapDerivedCategory := inferInstance
  have hHXSmall {I : Type (u + 1)} (K : Discrete I ⥤ _) : PreservesColimit K HX :=
    (hcolsSmall X).preservesColimitsOfShape.preservesColimit
  have : HY.IsEquivalence := hDEq Y
  have : (constantModelBoundedConstructible Λ' Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' Y).2.1
  let i : (lowerStar Λ p).rightDerivedFunctor ⋙ HY ≅
      HX ⋙ (lowerStar Λ' p).rightDerivedFunctor := derivedComapLowerStarIso e₀.inv p
  have hmap : ∀ K, localizingClosureProEtale Λ X K →
      localizingClosureProEtale Λ' X (HX.obj K) :=
    localizingClosure_map _ _ HX
      (fun K hK ↦ constantModelCtf_coefficientIso e X ⟨K, hK⟩)
      (fun _ K ↦ hHXSmall (K ⋙ (localizingClosureProEtale Λ X).ι))
  constructor
  · intro K
    have hK := constantModelCtf_coefficientIso e X K
    have ht := h.1 ⟨HX.obj K.obj, hK⟩
    have hi := i.app K.obj
    have hbc := (bounded_transport_iff e₀ Y _).mp
      ((constantModelBoundedConstructible Λ' Y).prop_of_iso hi.symm ht.1)
    obtain ⟨a, b, hab⟩ := ht.2
    refine ⟨hbc, a, b, ?_⟩
    apply DerivedCategory.torAmplitudeIn_of_torAmplitudeIn_mapDerivedCategory_obj (H Y)
    exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso hi.symm hab
  · intro I G
    let D := G ⋙ (localizingClosureProEtale Λ X).ι
    let G' := (localizingClosureProEtale Λ' X).lift (D ⋙ HX)
      (fun K ↦ hmap _ (G.obj K).property)
    have : PreservesColimit (G' ⋙ (localizingClosureProEtale Λ' X).ι)
        (lowerStar Λ' p).rightDerivedFunctor := h.2 I G'
    have : PreservesColimit (D ⋙ HX) (lowerStar Λ' p).rightDerivedFunctor :=
      preservesColimit_of_iso_diagram (lowerStar Λ' p).rightDerivedFunctor
        ((localizingClosureProEtale Λ' X).liftCompιIso (D ⋙ HX)
          (fun K ↦ hmap _ (G.obj K).property))
    have : PreservesColimit D HX := hHX D
    have : PreservesColimit D (HX ⋙ (lowerStar Λ' p).rightDerivedFunctor) :=
      comp_preservesColimit _ _
    have : PreservesColimit D ((lowerStar Λ p).rightDerivedFunctor ⋙ HY) :=
      preservesColimit_of_natIso D i.symm
    exact preservesColimit_of_reflects_of_preserves (lowerStar Λ p).rightDerivedFunctor HY

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]

include k in
private theorem properHypotheses_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (hsum : ProperUnboundedCoproductAssertions Λ.X p)
    (hloc : localizingClosure (constantModelBoundedConstructible Λ.X X) ≤
      fun K ↦ ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ.X X)
        ((DerivedCategory.homologyFunctor _ n).obj K)) :
    ProperLocalizingHypotheses Λ.X p := by
  have hc :
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with ⟨E, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  apply properHypotheses_of_bc Λ.X p
    (localizingClosure_ctf_equals_bc ℓ X Λ.X hc).1.2.2.1
    (localizingClosure_ctf_equals_bc ℓ Y Λ.X hc).1.2.2.1
  · intro K hK
    have hX := constantModelBoundedConstructible_eq_rational ℓ Λ hΛ k X
    have hY := constantModelBoundedConstructible_eq_rational ℓ Λ hΛ k Y
    apply (congrFun hY _).mpr
    have : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
    have : QuasiCompact (X.asOver (Spec (.of k))).hom :=
      inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
    have : IsSeparated (X.asOver (Spec (.of k))).hom :=
      inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
    have : LocallyOfFiniteType (Y.asOver (Spec (.of k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
    have : QuasiCompact (Y.asOver (Spec (.of k))).hom :=
      inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
    have : IsSeparated (Y.asOver (Spec (.of k))).hom :=
      inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
    have : IsProper (p.asOver (Spec (.of k))).left := inferInstanceAs (IsProper p)
    exact properPushforward_boundedConstructible_rational ℓ
      (p.asOver (Spec (.of k))) Λ hΛ K ((congrFun hX _).mp hK)
  · intro I K hK
    obtain ⟨c, hc, c', hc', _, _, hi⟩ := hsum.2 I K (fun i ↦ hloc _ (hK i))
    have := hi
    exact ⟨c, ⟨hc⟩, ⟨(Cofan.isColimitMapCoconeEquiv _ K c).2 hc'.ofPointIso⟩⟩

set_option linter.unusedSectionVars false in
include k in
private theorem geometricFibreBound : ∃ d : ℕ, ∀ y : Y, topologicalKrullDim
    (pullback p (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  refine ⟨d, fun y ↦ ?_⟩
  let t := CommRingCat.ofHom
    (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))
  calc
    _ = topologicalKrullDim (pullback (pullback.snd p (Y.fromSpecResidueField y))
        (Spec.map t) : Scheme.{u}) :=
      (IsHomeomorph.topologicalKrullDim_eq _
        ((pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
          (Spec.map t)).hom.homeomorph.isHomeomorph)).symm
    _ ≤ topologicalKrullDim (p.fiber y) := topologicalKrullDim_pullback_le_of_field _ _
    _ ≤ _ := hd y

include k in
private theorem properHypotheses_integral (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ProperLocalizingHypotheses (Profinite.padicIntegersRingObj ℓ E) p := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hc :
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
        Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
          Mon.mk (Profinite.padicIntegersRingObj ℓ E')) ∨
        Nonempty (Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
          Mon.mk (Profinite.continuousMapRingObj E'))) ∨
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
        Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩))
  obtain ⟨d, hd⟩ := geometricFibreBound k p
  have hs := integralProperDirectSums ℓ E k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos Fact.out X Y p d hd
  apply properHypotheses_of_bc _ p
    (localizingClosure_ctf_equals_bc ℓ X _ hc).1.2.2.1
    (localizingClosure_ctf_equals_bc ℓ Y _ hc).1.2.2.1
    (proper_integral_constructible ℓ E k X Y p)
  exact hs.2.2.2.2.2

include k in
private theorem properHypotheses_finite
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) :
    ProperLocalizingHypotheses (Profinite.continuousMapRingObj A) p := by
  classical
  let B := ULift.{u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have hB : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : B) = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
    change ULift.up ((ℓ ^ (n + 1) : ℕ) • (1 : A)) = ULift.up (0 : A)
    congr 1
    simp only [nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_pow, pow_succ, hn, zero_mul]
  have hf := finiteProperLocalizing ℓ (ringChar k) Fact.out
    (Fact.out : (ringChar k).Prime).pos Fact.out k B hB p
  let e : A ≃+* B := ULift.ringEquiv.symm
  let h : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheafOfUniverse.{u, u} B ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  have hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  let eb : Mon.mk (Profinite.continuousMapRingObj A) ≅
      Mon.mk (finiteDiscreteCondensedCoefficient B) := Mon.mkIso' E'
  apply properHypotheses_coefficientIso eb p
  refine ⟨fun K ↦ hf.1 _ K.property, ?_⟩
  intro I G
  exact hf.2.2.2 I (G ⋙ (localizingClosureProEtale _ X).ι)
    (fun i ↦ (G.obj ⟨i⟩).property)

end Coefficients

/-- In the standing separated finite-type positive-characteristic field setting,
both hypotheses of proper_image_localizing_proper hold for every admissible coefficient.
The list includes Q_ell and Z_ell explicitly, as the E = Q_ell specializations.

Source: blueprint proposition-proper-direct-image-extension-zero--1, coefficient assertions and
second proof paragraph (blueprint: proposition-proper-direct-image-extension-zero--1).

Proof: for E and Qbar, the schemes are qcqs by lem-weil-pbc-qcqs-over-affine.
By det-def-localizing-closure-ctf-equals-bc, Dctf equals Dbc, and the rational
proper base-change theorem proposition-proper-direct-image-constructible-complexes preserves Dbc.
By corollary-ambient-ind-derived their localizing closure lies in Dic;
sk-lem-proper-unbounded-window-ii therefore supplies exactly the required sums.
For finite A, corollary-proper-direct-image-finite-coefficients-localizing gives preservation of
Dctf and an exact sum-preserving restriction; its sums are ambient by fullness and sum
closure. No identification Dctf = Dbc for arbitrary finite A is used.
For O_E, qcqs again gives Dctf = Dbc; proposition-proper-direct-image-constructible-complexes
preserves Dbc. Properness and quasi-compactness of the target give a uniform
fibre-dimension bound by lem-fin-finite-type-fibre-dimension-bound, and
proposition-compactness-proper-direct-image--2 gives preservation of sums on that closure.
Taking E = Q_ell yields the Q_ell and Z_ell cases. -/
theorem proper_image_localizing_proper_coefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ProperLocalizingHypotheses Λ.X p := by
  have hp₀ : 0 < ringChar k := (Fact.out : (ringChar k).Prime).pos
  have hpℓ : ringChar k ≠ ℓ := Fact.out
  obtain ⟨d, hd⟩ := geometricFibreBound k p
  have hrat (F : PadicAlgCl.FiniteIntermediateField ℓ) :
      ProperLocalizingHypotheses (Profinite.continuousMapRingObj F) p := by
    apply properHypotheses_rational ℓ k p (Mon.mk _) (Or.inl ⟨F, rfl⟩)
      (properUnbounded_preservesCoproducts ℓ F k (ringChar k) hp₀ hpℓ X Y p d hd)
    exact (indConstructibleDerived_sums_and_truncations ℓ F k
      (ringChar k) hp₀ hpℓ X).2.2.2.2
  have hcl : ProperLocalizingHypotheses (Profinite.padicAlgClRingObj ℓ) p := by
    apply properHypotheses_rational ℓ k p (Mon.mk _) (Or.inr rfl)
      (properUnbounded_preservesCoproducts_padicAlgCl ℓ k
        (ringChar k) hp₀ hpℓ X Y p d hd)
    exact (indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k
      (ringChar k) hp₀ hpℓ X).2.2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ℓ
  let F₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at _hΛ
  rcases _hΛ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact properHypotheses_finite ℓ k p A _hA
  · exact properHypotheses_coefficientIso zIso p (properHypotheses_integral ℓ k p F₀)
  · exact properHypotheses_integral ℓ k p E
  · exact properHypotheses_coefficientIso qIso p (hrat F₀)
  · exact hrat E
  · exact hcl

end AlgebraicGeometry.ProEtale.CondensedRing
