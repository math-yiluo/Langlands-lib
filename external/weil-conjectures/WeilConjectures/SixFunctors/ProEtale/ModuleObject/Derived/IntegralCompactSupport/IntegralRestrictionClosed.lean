/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralComplementFiniteness
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Integral exceptional inverse image along a closed immersion

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-closed.md` (blueprint: theorem-f-shriek-ell-adic-coefficients--1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

private def comparisonEquiv
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : D ⥤ C) (H : C ⥤ D) (adj : F ⊣ H)
    (L : Q.FullSubcategory ⥤ P.FullSubcategory)
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) (adj' : L ⊣ G)
    (e : L ⋙ P.ι ≅ Q.ι ⋙ F)
    (A : Q.FullSubcategory) (K : P.FullSubcategory) :
    (A ⟶ G.obj K) ≃ (A.obj ⟶ H.obj K.obj) :=
  (adj'.homEquiv A K).symm.trans
    (P.fullyFaithfulι.homEquiv.trans
      ((Iso.homCongr (e.app A) (Iso.refl K.obj)).trans (adj.homEquiv _ _)))

private lemma comparisonEquiv_left
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : D ⥤ C) (H : C ⥤ D) (adj : F ⊣ H)
    (L : Q.FullSubcategory ⥤ P.FullSubcategory)
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) (adj' : L ⊣ G)
    (e : L ⋙ P.ι ≅ Q.ι ⋙ F)
    {A B : Q.FullSubcategory} (K : P.FullSubcategory)
    (f : A ⟶ B) (g : B ⟶ G.obj K) :
    comparisonEquiv P Q F H adj L G adj' e A K (f ≫ g) =
      f.hom ≫ comparisonEquiv P Q F H adj L G adj' e B K g := by
  simp only [comparisonEquiv, Equiv.trans_apply, adj'.homEquiv_naturality_left_symm]
  simp only [Functor.FullyFaithful.homEquiv, Iso.homCongr,
    Iso.refl_hom, Category.comp_id]
  change adj.homEquiv _ _
      (e.inv.app A ≫ ((L.map f).hom ≫ ((adj'.homEquiv B K).symm g).hom)) =
    f.hom ≫ adj.homEquiv _ _ (e.inv.app B ≫ ((adj'.homEquiv B K).symm g).hom)
  have he := e.inv.naturality f
  change F.map f.hom ≫ e.inv.app B = e.inv.app A ≫ (L.map f).hom at he
  rw [← Category.assoc, ← he, Category.assoc]
  exact adj.homEquiv_naturality_left f.hom _

private lemma comparisonEquiv_right
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : D ⥤ C) (H : C ⥤ D) (adj : F ⊣ H)
    (L : Q.FullSubcategory ⥤ P.FullSubcategory)
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) (adj' : L ⊣ G)
    (e : L ⋙ P.ι ≅ Q.ι ⋙ F)
    (A : Q.FullSubcategory) {K J : P.FullSubcategory}
    (f : A ⟶ G.obj K) (g : K ⟶ J) :
    comparisonEquiv P Q F H adj L G adj' e A J (f ≫ G.map g) =
      comparisonEquiv P Q F H adj L G adj' e A K f ≫ H.map g.hom := by
  simp only [comparisonEquiv, Equiv.trans_apply, adj'.homEquiv_naturality_right_symm]
  simp only [Functor.FullyFaithful.homEquiv, Iso.homCongr,
    Iso.refl_hom, Category.comp_id]
  change adj.homEquiv _ _
      (e.inv.app A ≫ (((adj'.homEquiv A K).symm f).hom ≫ g.hom)) =
    adj.homEquiv _ _ (e.inv.app A ≫ ((adj'.homEquiv A K).symm f).hom) ≫ H.map g.hom
  rw [← Category.assoc]
  exact adj.homEquiv_naturality_right _ g.hom

private def comparison
    (P : ObjectProperty C) (Q : ObjectProperty D) (S : ObjectProperty C)
    (F : D ⥤ C) (H : C ⥤ D) (adj : F ⊣ H)
    (L : Q.FullSubcategory ⥤ P.FullSubcategory)
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) (adj' : L ⊣ G)
    (e : L ⋙ P.ι ≅ Q.ι ⋙ F)
    (hS : S ≤ P) (hH : ∀ K, S K → Q (H.obj K)) :
    ObjectProperty.ιOfLE hS ⋙ G ⋙ Q.ι ≅ S.ι ⋙ H := by
  let R := Q.lift (S.ι ⋙ H) (fun K ↦ hH K.obj K.property)
  let φ (A : Q.FullSubcategory) (K : S.FullSubcategory) :
      (A ⟶ G.obj ((ObjectProperty.ιOfLE hS).obj K)) ≃ (A ⟶ R.obj K) :=
    (comparisonEquiv P Q F H adj L G adj' e A _).trans
      (Q.fullyFaithfulι.homEquiv (X := A) (Y := R.obj K)).symm
  let α (K : S.FullSubcategory) :
      G.obj ((ObjectProperty.ιOfLE hS).obj K) ≅ R.obj K :=
    Yoneda.ext _ _ (fun f ↦ φ _ K f) (fun f ↦ (φ _ K).symm f)
      (fun f ↦ (φ _ K).symm_apply_apply f)
      (fun f ↦ (φ _ K).apply_symm_apply f)
      (fun f g ↦ by
        apply Q.ι.map_injective
        simpa [φ, Functor.FullyFaithful.homEquiv] using
          comparisonEquiv_left P Q F H adj L G adj' e _ f g)
  exact NatIso.ofComponents (fun K ↦ Q.ι.mapIso (α K)) (by
    intro K J g
    change (G.map ((ObjectProperty.ιOfLE hS).map g)).hom ≫ (α J).hom.hom =
      (α K).hom.hom ≫ H.map g.hom
    have hleft := comparisonEquiv_left P Q F H adj L G adj' e
      ((ObjectProperty.ιOfLE hS).obj J)
      (G.map ((ObjectProperty.ιOfLE hS).map g)) (𝟙 _)
    have hright := comparisonEquiv_right P Q F H adj L G adj' e
      (G.obj ((ObjectProperty.ιOfLE hS).obj K)) (𝟙 _)
      ((ObjectProperty.ιOfLE hS).map g)
    simp only [Category.comp_id, Category.id_comp] at hleft hright
    simpa [α, Yoneda.ext, Yoneda.fullyFaithful, φ,
      Functor.FullyFaithful.homEquiv, ObjectProperty.fullyFaithfulι] using hleft.symm.trans hright)

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

private theorem generators_mem_localizing (Λ : Sheaf (coherentTopology Profinite.{u})
    Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ∀ K, generators Λ X K → localizing Λ X K := by
  intro K hK P _ hP
  exact hP K hK

private theorem closedCompactificationComparison (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    [PreservesFiniteColimits (lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i)]
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) Z K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K)) :
    Nonempty (lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⋙
        (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).ι ≅
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).ι ⋙
        (lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).mapDerivedCategory) := by
  obtain ⟨_, φ, _, _⟩ := integralLocalizingCompactSupport ℓ E k
  let Z' : Spaces k := ⟨Over.mk (Z ↘ Spec (.of k)),
    by
      change IsSeparated (Z ↘ Spec (.of k)) ∧
        LocallyOfFiniteType (Z ↘ Spec (.of k)) ∧ QuasiCompact (Z ↘ Spec (.of k))
      exact ⟨inferInstance, inferInstance, inferInstance⟩⟩
  let X' : Spaces k := ⟨Over.mk (X ↘ Spec (.of k)),
    by
      change IsSeparated (X ↘ Spec (.of k)) ∧
        LocallyOfFiniteType (X ↘ Spec (.of k)) ∧ QuasiCompact (X ↘ Spec (.of k))
      exact ⟨inferInstance, inferInstance, inferInstance⟩⟩
  let f : Z' ⟶ X' := ObjectProperty.homMk (Over.homMk i)
  let d : Compactifications k f := ⟨Compactification.ofIsProper i, by
    change QuasiCompact (𝟙 Z)
    infer_instance⟩
  refine ⟨φ f c.obj d ≪≫ ?_⟩
  exact
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
        (derivedOpenImmersionLowerShriekId (Profinite.padicIntegersRingObj ℓ E.val) Z) _ ≪≫
        Functor.leftUnitor _ ≪≫
        Functor.rightDerivedFunctorIsoMapDerivedCategory
          (lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i))

/-- The inclusion of finite-constant bounded constructible complexes into the integral
localizing category.  This records the ambient category in which the Brown right adjoint
is compared with sections with support.
Source: blueprint `definition-localizing-subcategory` and
`theorem-f-shriek-ell-adic-coefficients--1` (blueprint:
theorem-f-shriek-ell-adic-coefficients--1). -/
def generatorsToLocalizing {X : Scheme.{u}}
    (h : ∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X K) :
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).ι
    (fun K ↦ h K.obj K.property)

/-- The assertion package for integral closed restriction.  The first clause is bounded
constructibility of derived sections with support.  The second clause says that, on the
bounded-constructible generators, this support functor is naturally isomorphic to every
right adjoint supplied by the integral Brown theorem, for every boundary compactification.
Source: blueprint `sk-thm-int-restriction-closed.md`, both displayed clauses
(blueprint: theorem-f-shriek-ell-adic-coefficients--1). -/
def integralRestrictionClosedAssertions {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of k))]
    (hAdd : (closedModuleSectionsWithSupport
      (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).Additive) : Prop := by
  letI := hAdd
  exact ∃ hgen : ∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X K,
    (∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
      generators (Profinite.padicIntegersRingObj ℓ E.val) Z
        (((closedModuleSectionsWithSupport
          (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).rightDerivedFunctor).obj
          K)) ∧
    (∀ (c : Compactification.BoundaryCompactification i)
      (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) Z K →
        localizing (Profinite.padicIntegersRingObj ℓ E.val) X
          ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
      (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
        (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).FullSubcategory)
      (_adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G),
      Nonempty
        (generatorsToLocalizing ℓ E hgen ⋙ G ⋙
            (localizing (Profinite.padicIntegersRingObj ℓ E.val) Z).ι ≅
          (generators (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
            (closedModuleSectionsWithSupport
              (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).rightDerivedFunctor))

/-- For a closed immersion over a finite-type separated scheme over a field, derived sections
with support along the canonical open complement preserve bounded constructibility and identify
naturally with the integral exceptional inverse image.  The latter is the right adjoint of the
integral Brown compact-support functor, independently of the chosen boundary compactification.
Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-closed.md` (blueprint: theorem-f-shriek-ell-adic-coefficients--1).

Proof plan (the node's steps):
1. Let `j : U ⟶ X` be the open complement `i.openComplement.ι`.  `k` is Noetherian, so `X` is
   Noetherian (lem-weil-pbc-finite-type-over-noetherian) and every open of `X` is
   quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian); hence `j` is
   quasi-compact, of finite type (lem-weil-pbc-qc-open-immersion-finite-type) and separated
   (lem-weil-pbc-separated-cancellation (a)).  `U` with `a_X ∘ j` is a standing scheme
   (lem-weil-pbc-proper-fp-permanence (e), def-weil-finite-type-morphism).  The pulled-back
   `O_E` is admissible in lemma-sections-support-closed-subscheme--1; its (2) makes `i_*` exact.
2. `i` is proper (lem-weil-pbc-closed-immersion-proper (a)); use the compactification
   `(id_Z, i)`.  The formula and comparison of proposition-construction-independence-rf-shriek give
   `Ri_! ≅ Ri_* D((id_Z)_!) = Ri_*`, and exactness of `i_*` gives `Ri_* ≅ i_*`.
3. lemma-sections-support-closed-subscheme (1),(3) with `Λ = O_E`: the natural triangle
   `F → K → Rj_* j^* K → F[1]` with `F = i_* RΓ_Z K`, the fibre formula
   `RΓ_Z K ≅ i^* F`, and the adjunction `Hom_X(i_* A, K) ≃ Hom_Z(A, RΓ_Z K)`.
4. lemma-inverse-image-tensor-product (1) for `j`: `J = j^* K ∈ Dbc(U, O_E)`.
5. proposition-direct-image-along-open-immersion--1 for `J` and the quasi-compact open immersion
`j`:
   `C = Rj_* J ∈ Dbc(X, O_E)`.
6. lemma-structure-integral-constructible-complexes--1 (1): `Dbc(X, O_E)` is triangulated.  Rotating
   (TR2 of def-weil-triangulated-category) to `C[-1] → F → K → C`, the two-out-of-three
   condition of def-weil-triangulated-subcategory gives `F ∈ Dbc(X, O_E)`.
7. lemma-inverse-image-tensor-product (1) for `i`: `i^* F ∈ Dbc(Z, O_E)`; by the fibre formula and
   isomorphism invariance (definition-constructible-sheaves), `RΓ_Z K ∈ Dbc(Z, O_E)`.  This is the
   first clause.
8. Put `B = i^! K` (from `G`, the right adjoint of theorem-existence-exceptional-inverse-image for
`c`) and
   `H = RΓ_Z K`.  With det-def-localizing-closure-ctf-equals-bc (2), `K`, `H`, `B` lie in
   the localizing categories (definition-localizing-subcategory, full).  For `A` in `Loc(Dbc(Z))`,
   the Brown bijection, step 2 and step 3 give
   `Φ_A : Hom(A, B) ≃ Hom(i_* A, K) ≃ Hom(A, H)`, natural in `A` and `K`.
9. Yoneda: `α_K = Φ_B (𝟙 B)` and `β_K = Φ_H⁻¹ (𝟙 H)` are inverse, and naturality of `Φ` in
   `K` makes `α` natural; restricted to generators this is the second clause. -/
theorem integralRestrictionClosed (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of k))] :
    ∃ hAdd : (closedModuleSectionsWithSupport
      (Profinite.padicIntegersRingObj ℓ E.val) i i.openComplement.ι).Additive,
      integralRestrictionClosedAssertions (k := k) ℓ E i hAdd := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have hij : Set.range i.openComplement.ι = (Set.range i)ᶜ := by
    rw [i.range_eq_compl_range_openComplement_ι, compl_compl]
  obtain ⟨hAdd, adj, _, _, ⟨δ, hδ⟩, _⟩ :=
    formal_closed_support_derived Λ ℓ k hΛ i i.openComplement.ι hij
  let := hAdd
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨hclosed, _, _, _, _, _, _, _, _, _, hfull, hfaith, ⟨ei⟩, _⟩ :=
    condensed_open_closed_recollement Λ i i.openComplement.ι hij
  let := hclosed
  let := hfull
  let := hfaith
  have hfin := integralComplementFiniteness ℓ E k i
  let := hfin.1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ Z).2.1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  have hc : ∀ K, generators Λ X K → generators Λ Z
      ((closedModuleSectionsWithSupport Λ i i.openComplement.ι).rightDerivedFunctor.obj K) := by
    intro K hK
    have hF : generators Λ X
        (((closedModuleSectionsWithSupport Λ i i.openComplement.ι).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory).obj K) := by
      exact (generators Λ X).ext_of_isTriangulatedClosed₁ _ (hδ K) hK (hfin.2 K hK)
    have hP := (integralModels_operations ℓ E).1 i _ hF
    let eD := Functor.mapDerivedCategoryCompIso (lowerStar Λ i) (upperStar Λ i) ≪≫
      Functor.mapDerivedCategoryNatIso ei ≪≫ Functor.mapDerivedCategoryIdIso _
    exact (generators Λ Z).prop_of_iso (eD.app _) hP
  refine ⟨hAdd, ?_⟩
  refine ⟨generators_mem_localizing Λ X, hc, ?_⟩
  intro c h G adjG
  obtain ⟨e⟩ := closedCompactificationComparison ℓ E k i c h
  refine ⟨?_⟩
  exact comparison (localizing Λ X) (localizing Λ Z) (generators Λ X)
    (lowerStar Λ i).mapDerivedCategory
    (closedModuleSectionsWithSupport Λ i i.openComplement.ι).rightDerivedFunctor
    adj.mapDerivedCategoryRightDerivedAdjunction _ G adjG e
    (generators_mem_localizing Λ X)
    (fun K hK ↦ generators_mem_localizing Λ Z _ (hc K hK))

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
