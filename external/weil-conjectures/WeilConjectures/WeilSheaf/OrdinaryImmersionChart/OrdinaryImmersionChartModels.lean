/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
public import WeilConjectures.CategoryTheory.SubterminalImageCalculus.SubterminalDerivedImageCalculus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Ordinary immersion and representable-chart comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
lemma-derived-pullback-composition; sites-modules.tex, Tag 04IF,
lemma-localize-morphism-ringed-topoi; Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-tw-ordinary-immersion-chart-models).

All pullbacks below are ordinary, before completion. The records retain their
universal computation counits and the ordinary adjunction mates that normalize
both comparisons. Schemes and coefficients have independent universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OrdinaryImmersionChart

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The underlying ring sheaf of the recorded commutative completed coefficient sheaf.
Source: Stacks 03CO (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
@[irreducible]
def Rings (T : Scheme.{t}) : Sheaf (ProEt.topology T) RingCat.{max u (t + 1)} :=
  completedIntegralCoefficientSheafUnrestricted l E T

/-- The recorded module-sheaf category over the completed ring, with no completeness
condition on its objects. Source: Stacks 03DA, 0D6D
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
abbrev Modules (T : Scheme.{t}) :=
  ringedSiteModules.{max u (t + 1)} (Rings l E T)

attribute [local semireducible] Rings

/-- The adjunct of exactly the projection-defined structural map c_g.
Source: Stacks 04J0 (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
def directRingMap {T W : Scheme.{t}} (g : T ⟶ W) :
    Rings l E W ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology W) (ProEt.topology T)).obj
          (Rings l E T) :=
  ⟨Functor.whiskerRight
    (((completedRingAdj.{t, u} g).homEquiv _ _) (completedRingMap l E g)).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- Ordinary sectionwise module direct image, with action through the structural adjunct.
Source: Stacks 03D1 (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
abbrev push {T W : Scheme.{t}} (g : T ⟶ W) : Modules l E T ⥤ Modules l E W :=
  SheafOfModules.pushforward.{max u (t + 1)} (directRingMap l E g)

/-- Mathlib's sheafified module Kan extension: B_T tensor_(g⁻¹ B_W) g⁻¹(-).
The left adjoint is selected by its universal property, not by an arbitrary map.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
@[irreducible]
def pull {T W : Scheme.{t}} (g : T ⟶ W) : Modules l E W ⥤ Modules l E T :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  SheafOfModules.pullback.{max u (t + 1)} (directRingMap l E g)

/-- The canonical ordinary pullback adjunction, including its tensor-generator unit.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
@[irreducible]
def adj {T W : Scheme.{t}} (g : T ⟶ W) : pull l E g ⊣ push l E g := by
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (directRingMap l E g)
  unfold pull
  exact SheafOfModules.pullbackPushforwardAdjunction (directRingMap l E g)

/-- Additivity supplied by the existing sectionwise pushforward and adjunction APIs.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
instance pullAdditive {T W : Scheme.{t}} (g : T ⟶ W) : (pull l E g).Additive :=
  letI := CategoryTheory.SubterminalImageCalculus.pushforwardAdditive (directRingMap l E g)
  (adj l E g).left_adjoint_additive

/-- Flat-term K-flat representatives use the recorded independent-universe predicates.
Source: Stacks 06YN, 06YS (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
def Good (T : Scheme.{t}) (P : CochainComplex (Modules l E T) ℤ) : Prop :=
  @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
    T.ProEt inferInstance (essentiallySmallSelf _) (ProEt.topology T)
      (completedIntegralCommRingSheafUnrestricted l E T) P ∧ ∀ n : ℤ,
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted l E T) (P.X n)

/-- An ordinary derived pullback, with its universal counit and K-flat computation.
Existence of these models is part of the conclusion, not an additional hypothesis.
Source: Stacks 06YY, 0D6D
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
structure Image {T W : Scheme.{t}} (g : T ⟶ W) [(pull l E g).Additive] where
  functor : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Modules l E T)
  counit : DerivedCategory.Q ⋙ functor ⟶
    (pull l E g).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Modules l E W) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules l E W) ℤ,
    Good l E W P → IsIso (counit.app P)

/-- Exact restriction to a represented slice identified with the site of its scheme.
The coefficient isomorphism is uniquely determined by the constant-section and finite
projection equations in completedRingMap_slice; the identity morphism merely obtains
that same identification without making it depend on a second scheme morphism.
Source: Stacks 04IF, 04J0
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
def chartRingIso {W : Scheme.{t}} (U : W.ProEt) :
    (completedRingRestriction.{t, u} U).obj
      (completedIntegralCommRingSheafUnrestricted l E W) ≅
        completedIntegralCommRingSheafUnrestricted l E U.left :=
  (completedRingMap_slice l E (𝟙 W) U).choose

/-- Sectionwise restriction, followed by the recorded slice equivalence and its
projection-normalized coefficient transport. Source: Stacks 04IF, 04J0
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
abbrev restrict {W : Scheme.{t}} (U : W.ProEt) : Modules l E W ⥤ Modules l E U.left :=
  letI := ProEt.sliceDense W U
  letI : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology W) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward.{max u (t + 1)}
    (F := MorphismProperty.Over.map ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology W)
    (S := Rings l E U.left)
    (R := Rings l E W)
    ⟨Functor.whiskerRight (chartRingIso l E U).inv.hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The base-change comparison on the two equal composites, fixed by the actual
fibre-product compositors. Source: Stacks 0D6D, 04J0
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
def squareSiteIso {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d) :
    proEtaleBaseChange b ⋙ proEtaleBaseChange a ≅
      proEtaleBaseChange d ⋙ proEtaleBaseChange c :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a b).symm ≪≫
    eqToIso (congrArg (fun g : A ⟶ D ↦ proEtaleBaseChange g) e) ≪≫
      MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) c d

/-- Normalization of an ordinary square by sectionwise direct image and its
adjunction mate. It is the composite of the ordinary composition comparisons
and transport along the specified equality, with all coefficient actions retained.
Source: Stacks 0D6D, 04J0
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
structure Square {A B C D : Scheme.{t}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (e : a ≫ b = c ≫ d) where
  direct : push l E c ⋙ push l E d ≅ push l E a ⋙ push l E b
  sections : ∀ (N : Modules l E A) (H : D.ProEt)
    (m : ((push l E c ⋙ push l E d).obj N).val.obj (op H)),
    (direct.hom.app N).val.app (op H) m =
      N.val.map ((squareSiteIso a b c d e).hom.app H).op m
  ordinary : pull l E b ⋙ pull l E a ≅ pull l E d ⋙ pull l E c
  mate : conjugateIsoEquiv ((adj l E d).comp (adj l E c))
    ((adj l E b).comp (adj l E a)) ordinary = direct

/-- The first comparison together with its ordinary K-flat representative equation.
The second pullbacks use immersion restrictions: their computation counits are
invertible on every complex, not only on complete objects.
Source: Stacks 0D6D; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
structure ImmersionSquare {X Y S : Scheme.{t}} (f : X ⟶ Y) (i : S ⟶ Y)
    [(pull l E f).Additive] [(pull l E i).Additive]
    [(pull l E (pullback.fst f i)).Additive]
    [(pull l E (pullback.snd f i)).Additive]
    (Pf : Image l E f) (Pi : Image l E i)
    (Pj : Image l E (pullback.fst f i)) (Ps : Image l E (pullback.snd f i)) where
  iLimits : PreservesFiniteLimits (pull l E i)
  iColimits : PreservesFiniteColimits (pull l E i)
  jLimits : PreservesFiniteLimits (pull l E (pullback.fst f i))
  jColimits : PreservesFiniteColimits (pull l E (pullback.fst f i))
  iExact : ∀ Q : CochainComplex (Modules l E Y) ℤ, IsIso (Pi.counit.app Q)
  jExact : ∀ Q : CochainComplex (Modules l E X) ℤ, IsIso (Pj.counit.app Q)
  square : Square l E (pullback.fst f i) f (pullback.snd f i) i
    (pullback.condition (f := f) (g := i))
  comparison : Pf.functor ⋙ Pj.functor ≅ Pi.functor ⋙ Ps.functor
  normalization : ∀ Q : CochainComplex (Modules l E Y) ℤ, Good l E Y Q →
    comparison.hom.app (DerivedCategory.Q.obj Q) ≫
        Ps.functor.map (Pi.counit.app Q) ≫
          Ps.counit.app (((pull l E i).mapHomologicalComplex (.up ℤ)).obj Q) =
      Pj.functor.map (Pf.counit.app Q) ≫
        Pj.counit.app (((pull l E f).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex square.ordinary (.up ℤ)).hom.app Q)

/-- Additivity of restriction is the existing sectionwise pushforward instance.
Source: Stacks 04IF (blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
instance restrictAdditive {W : Scheme.{t}} (U : W.ProEt) : (restrict l E U).Additive :=
  letI : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology W) := ProEt.isContinuous_overMap U.prop
  CategoryTheory.SubterminalImageCalculus.pushforwardAdditive _

/-- The representable slice comparison, with its ordinary mate and K-flat equation.
The right-adjoint equation fixes the localized morphism on the actual base-changed
schemes. Its coefficient actions are those of directRingMap and chartRingIso, so it
identifies ringed morphisms. The ordinary mate is fixed by the unit and counit.
Source: Stacks 04IF and 0D6D
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
structure Chart {T S : Scheme.{t}} (g : T ⟶ S) (U : S.ProEt)
    (Pg : Image l E g) (Pv : Image l E (completedRingSliceArrow g U)) where
  uLimits : PreservesFiniteLimits (restrict l E U)
  uColimits : PreservesFiniteColimits (restrict l E U)
  vLimits : PreservesFiniteLimits (restrict l E ((proEtaleBaseChange g).obj U))
  vColimits : PreservesFiniteColimits (restrict l E ((proEtaleBaseChange g).obj U))
  rU : CompletedCoefficientPushforward.ExactImage (restrict l E U)
  rV : CompletedCoefficientPushforward.ExactImage (restrict l E ((proEtaleBaseChange g).obj U))
  direct : push l E g ⋙ restrict l E U ≅
    restrict l E ((proEtaleBaseChange g).obj U) ⋙ push l E (completedRingSliceArrow g U)
  sections : ∀ (N : Modules l E T) (H : U.left.ProEt)
    (m : ((push l E g ⋙ restrict l E U).obj N).val.obj (op H)),
    (direct.hom.app N).val.app (op H) m =
      N.val.map (completedRingSlicePointIso g U H).hom.op m
  ordinary : restrict l E U ⋙ pull l E (completedRingSliceArrow g U) ≅
    pull l E g ⋙ restrict l E ((proEtaleBaseChange g).obj U)
  mate : ∀ M : Modules l E S, ordinary.hom.app M =
    (pull l E (completedRingSliceArrow g U)).map
      ((restrict l E U).map ((adj l E g).unit.app M)) ≫
    (pull l E (completedRingSliceArrow g U)).map
      (direct.hom.app ((pull l E g).obj M)) ≫
    (adj l E (completedRingSliceArrow g U)).counit.app
      ((restrict l E ((proEtaleBaseChange g).obj U)).obj ((pull l E g).obj M))
  comparison : rU.functor ⋙ Pv.functor ≅ Pg.functor ⋙ rV.functor
  normalization : ∀ Q : CochainComplex (Modules l E S) ℤ, Good l E S Q →
    comparison.hom.app (DerivedCategory.Q.obj Q) ≫
        rV.functor.map (Pg.counit.app Q) ≫
          rV.factors.hom.app (((pull l E g).mapHomologicalComplex (.up ℤ)).obj Q) =
      Pv.functor.map (rU.factors.hom.app Q) ≫
        Pv.counit.app (((restrict l E U).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app Q)

/-- The two comparisons and the formula defining the second from the first and the
inverse slice comparison. Every component is a natural isomorphism on the entire
ordinary unbounded derived category. Source: Stacks 0D6D, 04IF
(blueprint: lem-tw-ordinary-immersion-chart-comparison). -/
structure Comparison {X Y S : Scheme.{t}} (f : X ⟶ Y) (i : S ⟶ Y) (U : S.ProEt) where
  Pf : Image l E f
  Pi : Image l E i
  Pj : Image l E (pullback.fst f i)
  Ps : Image l E (pullback.snd f i)
  Pv : Image l E (completedRingSliceArrow (pullback.snd f i) U)
  immersion : ImmersionSquare l E f i Pf Pi Pj Ps
  chart : Chart l E (pullback.snd f i) U Ps Pv
  comparison : (Pf.functor ⋙ Pj.functor) ⋙ chart.rV.functor ≅
    (Pi.functor ⋙ chart.rU.functor) ⋙ Pv.functor
  formula : comparison =
    isoWhiskerRight immersion.comparison chart.rV.functor ≪≫
      Functor.associator Pi.functor Ps.functor chart.rV.functor ≪≫
        isoWhiskerLeft Pi.functor chart.comparison.symm ≪≫
          (Functor.associator Pi.functor chart.rU.functor Pv.functor).symm

end WeilConjectures.OrdinaryImmersionChart
