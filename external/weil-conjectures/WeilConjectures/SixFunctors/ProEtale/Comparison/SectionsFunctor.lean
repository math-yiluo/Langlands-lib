/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Sections of pro-étale sheaves and their derived functors

The sections functors of the small pro-étale site, the reduction of the vanishing of derived
sections over an object `T` of the pro-étale site to the derived global sections of the
pullback to `T`, and the commutation `g^* ν^* ≅ ν^* g^*` of the comparison pullbacks with
pullbacks.

## Main definitions

- `AlgebraicGeometry.ProEtale.sectionsFunctor`: evaluation at an object of the pro-étale site.
- `AlgebraicGeometry.ProEtale.globalSectionsFunctor`: the global sections functor.
- `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`: `g^* ν_X^* ≅ ν_Y^* g^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Evaluation of pro-étale sheaves at an object of the pro-étale site. -/
noncomputable abbrev sectionsFunctor {X : Scheme.{u}} (Y : X.ProEt) :
    Sheaf (ProEt.topology X) A ⥤ A :=
  sheafToPresheaf (ProEt.topology X) A ⋙ (evaluation _ A).obj (op Y)

/-- A short complex of pro-étale sheaves is exact if the short complexes of sections over all
objects of the affine pro-étale site are exact. -/
lemma ShortComplex.exact_of_exact_sectionsFunctor {X : Scheme.{u}}
    (S : ShortComplex (Sheaf (ProEt.topology X) A))
    (h : ∀ W : X.AffineProEt,
      (S.map (sectionsFunctor A ((AffineProEt.toProEt X).obj W))).Exact) : S.Exact := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let Φ := (AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
    (ProEt.topology X)
  have : LocallySmall.{u + 1} X.AffineProEt := ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  have : EssentiallySmall.{u + 1} X.AffineProEt := essentiallySmall_of_small_of_locallySmall _
  have : HasSheafify (AffineProEt.topology X) A :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall A _
  have : Abelian (Sheaf (AffineProEt.topology X) A) := sheafIsAbelian
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  -- the presheaves underlying the restriction to the affine site form an exact short complex
  let T := (S.map Φ).map (sheafToPresheaf (AffineProEt.topology X) A)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact fun W ↦ h W.unop
  -- sheafifying it gives back the restriction, sheafification being exact
  have : (presheafToSheaf (AffineProEt.topology X) A).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineProEt.topology X) A)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm

/-- The global sections functor of the small pro-étale site: the sections over the terminal
object. -/
noncomputable abbrev globalSectionsFunctor (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) A ⥤ A :=
  sectionsFunctor A (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))

/-- **Derived sections over an object of the pro-étale site.** For `T` an object of the small
pro-étale site of `X`, the derived sections over `T` of a pro-étale sheaf `G` on `X` are the
derived global sections of its pullback to `T`: the pullback is the restriction to the
localization `T_proét` of `X_proét`, which is exact and preserves injectives. -/
lemma isZero_rightDerived_sectionsFunctor_of_upperStar {X : Scheme.{u}} (T : X.ProEt)
    (G : Sheaf (ProEt.topology X) A) (q : ℕ)
    (h : IsZero (((globalSectionsFunctor A T.left).rightDerived q).obj
      ((ProEtale.upperStar A T.hom).obj G))) :
    IsZero (((sectionsFunctor A T).rightDerived q).obj G) := by
  have hT : WeaklyEtale T.hom := T.prop
  let j := ProEtale.localizationRestriction A T.hom hT
  -- `T` is the image of the terminal object of `T_proét` under the localization functor
  let e : T ≅ (MorphismProperty.Over.map ⊤ hT).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 T.left) (MorphismProperty.id_mem _ T.left)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  have : j.Additive := { }
  let eΓ : sectionsFunctor A T ≅ j ⋙ globalSectionsFunctor A T.left :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.inv.op).symm)
  let eR : (sectionsFunctor A T).rightDerived q ≅
      (j ⋙ globalSectionsFunctor A T.left).rightDerived q :=
    { hom := NatTrans.rightDerived eΓ.hom q
      inv := NatTrans.rightDerived eΓ.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id] }
  have : PreservesFiniteColimits j :=
    preservesFiniteColimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  have : PreservesFiniteLimits j :=
    preservesFiniteLimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  refine IsZero.of_iso ?_ (eR.app G ≪≫
    (Functor.rightDerivedCompIsoOfExact j (globalSectionsFunctor A T.left) q).app G)
  exact h.of_iso (((globalSectionsFunctor A T.left).rightDerived q).mapIso
    ((ProEtale.upperStarIsoLocalizationRestriction A T.hom hT).app G).symm)

/-- The comparison pullbacks commute with pullback along any morphism `g : Y ⟶ X`:
`g^* ν_X^* ≅ ν_Y^* g^*`, both being left adjoint to `ν_X_* g_* ≅ g_* ν_Y_*`. -/
noncomputable def comparisonUpperStarCompUpperStarIso {Y X : Scheme.{u}} (g : Y ⟶ X) :
    comparisonUpperStar A X ⋙ ProEtale.upperStar A g ≅
      Etale.upperStar A g ⋙ comparisonUpperStar A Y :=
  (conjugateIsoEquiv ((Etale.upperStarLowerStarAdjunction A g).comp (comparisonAdjunction A Y))
    ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A g))).symm
    (lowerStarCompComparisonLowerStarIso g A).symm

end AlgebraicGeometry.ProEtale
