/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.AlgebraicGeometry.ProjectionSection.ModuleProjectionSectionArrows
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
/-!
# Integral compact support on the ordinary localizing category

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-brown,
sk-prop-int-brown-construction (blueprint: proposition-construction-independence-rf-shriek).

The auxiliary names package the actual module-object functors and their adjunction
mates. The generators use finite constant scalar models, and all coproducts are
ordinary ambient coproducts, without a derived-completeness condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- This class-valued definition is intentionally semireducible: it caches the data.
set_option warn.classDefReducibility false in
/-- A named copy of the canonical coefficient-ring multiplication.

Keeping this instance named prevents repeated expansion of the valuation ring and
its sheafification when checking derived comparison components.
Source: the canonical condensed ring of integers of E
(blueprint: def-sfb-integral-compact-support-interface). -/
def integralCoefficientMonObj (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    MonObj (Profinite.padicIntegersRingObj.{u} ℓ E.val) := inferInstance

set_option warn.classDefReducibility false in
attribute [local instance 6000] integralCoefficientMonObj

/-- The existing unbounded category, abbreviated solely to display the comparison maps.
Source: blueprint sk-prop-int-brown-construction, coefficient convention
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev Ambient (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The actual total derived inverse image of module objects.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ Y ⥤ Ambient Λ X :=
  moduleDerivedPullback Λ f

/-- The actual total right-derived direct image of module objects.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) : Ambient Λ X ⥤ Ambient Λ Y :=
  moduleDerivedPushforward Λ f

/-- Exact, termwise extension by zero.
Source: blueprint sk-prop-int-brown-construction, displayed composite
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev extend {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Ambient Λ X ⥤ Ambient Λ Y :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The existing compactification composite, with no new choice of compactification.
Source: blueprint sk-prop-int-brown-construction, displayed formula
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Ambient Λ X ⥤ Ambient Λ Y :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- The recorded finite-constant-model bounded constructible generators.
Source: blueprint sk-prop-int-brown-construction and definition-constructible-sheaves
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev generators (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  constantModelBoundedConstructible Λ X

/-- Loc of Dbc, formed by the recorded ordinary localizing-closure operation.
Source: blueprint sk-prop-int-brown-construction, first paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
def localizing (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  CategoryTheory.localizingClosure (generators Λ X)

/-- The open adjunction with the actual total derived pullback, transported along
its canonical identification with the levelwise pullback.
Source: blueprint sk-prop-int-brown-construction, comparison construction
(blueprint: proposition-construction-independence-rf-shriek). -/
def openAdjunction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    extend Λ j ⊣ pull Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- The pullback-square comparison, using the given equality of scheme morphisms.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: proposition-construction-independence-rf-shriek). -/
def pullSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    pull Λ v ⋙ pull Λ f' ≅ pull Λ f ⋙ pull Λ u' :=
  (leftDerivedUpperStarComp Λ f' v).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y => pull Λ h) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ u' f

/-- The proper direct-image exchange: unit, square transport, then counit.
This definition makes sense before asserting that the map is invertible.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
def pushExchange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : CommSq u' f' f v) :
    push Λ f ⋙ pull Λ v ⟶ pull Λ u' ⋙ push Λ f' :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (derivedUpperStarLowerStarAdjunction Λ f').unit ≫
    (Functor.squareTransport (push Λ f) (push Λ f') (pullSquare Λ sq)).hom ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ f).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The open exchange in its mate direction, again before asserting invertibility.
Source: blueprint sk-prop-int-brown-construction, proof final paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
def openExchange {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {w : Z' ⟶ Z} {j' : X' ⟶ Z'} {u' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq u' j' j w) :
    pull Λ u' ⋙ extend Λ j' ⟶ extend Λ j ⋙ pull Λ w :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (openAdjunction Λ j).unit _ ≫
    (Functor.squareTransport (extend Λ j) (extend Λ j')
      (pullSquare Λ sq.flip)).hom ≫
    Functor.whiskerLeft _ (openAdjunction Λ j').counit ≫
    (Functor.rightUnitor _).hom

/-- Canonical composition of total derived pushforwards, conjugate to pullback
composition under the recorded derived adjunctions.
Source: blueprint sk-prop-int-brown-construction, compactification comparisons
(blueprint: proposition-construction-independence-rf-shriek). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push Λ f ⋙ push Λ g ≅ push Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction Λ g).comp
      (derivedUpperStarLowerStarAdjunction Λ f))
    (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (leftDerivedUpperStarComp Λ f g)

/-- The restriction map which normalizes a proper-open refinement comparison.
It uses pullback composition followed by the actual proper adjunction counit.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: proposition-construction-independence-rf-shriek). -/
def refinementRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :
    (pull Λ d.i).obj ((push Λ r.hom).obj ((extend Λ c.i).obj K)) ⟶
      (pull Λ c.i).obj ((extend Λ c.i).obj K) :=
  ((eqToIso (congrArg (fun h : X ⟶ d.Z => pull Λ h) r.i_hom.symm) ≪≫
    leftDerivedUpperStarComp Λ c.i r.hom).hom.app _) ≫
      (pull Λ c.i).map
        ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app _)

/-- The normalized refinement comparison, once its proper-open isomorphism is given.
The latter will be required to satisfy the open-adjunction normalization in the theorem.
Source: blueprint sk-prop-int-brown-construction, comparison proof
(blueprint: proposition-construction-independence-rf-shriek). -/
def refinementIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K)) :
    (image Λ c).obj K ≅ (image Λ d).obj K :=
  ((pushComp Λ r.hom d.g ≪≫
    eqToIso (congrArg (fun h : c.Z ⟶ Y => push Λ h) r.hom_g)).symm.app _) ≪≫
      (push Λ d.g).mapIso e.symm

/-- The specified proper/open exchange and its component API, kept as one structure.
The source of the proper pullback is explicitly the base-changed compactification,
so its module-object category is shared by the two exchange factors.
Source: blueprint sk-prop-int-brown-construction, final base-change composite
(blueprint: def-sfb-integral-compact-support-interface). -/
def baseChangeData {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :=
  letI := h
  (Functor.compactSupportExchangeData (extend Λ c.i) (push Λ c.g) (pull Λ v)
    (pull Λ (X := (c.ofIsPullback sq).Z) (pullback.fst c.g v))
    (push Λ (c.ofIsPullback sq).g) (pull Λ u')
    (extend Λ (c.ofIsPullback sq).i)
    (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).symm)

/-- The compact-support base-change map: proper exchange followed by inverse open
exchange, with the latter inverse specified by an `IsIso` proof, never chosen freely.
Source: blueprint sk-prop-int-brown-construction, last paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
def baseChange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :
    image Λ c ⋙ pull Λ v ⟶ pull Λ u' ⋙ image Λ (c.ofIsPullback sq) :=
  (baseChangeData Λ c sq h).map

/-- Componentwise invertibility of the compact-support exchange composite.
Proof: the proper exchange component is invertible by hypothesis; functors preserve
isomorphisms, so the proper image of the inverse open exchange is invertible too.
Their composite is the specified base-change component.
Source: blueprint sk-prop-int-brown-construction, final base-change composite
(blueprint: def-sfb-integral-compact-support-interface). -/
theorem baseChangeIsIsoOfProper
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (hp : IsIso ((pushExchange Λ
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app ((extend Λ c.i).obj K))) :
    IsIso ((baseChange Λ c sq ho).app K) := by
  exact (baseChangeData Λ c sq ho).isIso K hp

variable (k : Type u) [Field k]

/-- The full category of the standing separated finite-type k-schemes. Bundling over
Spec k ensures that every morphism is a k-morphism, with no extra condition on it.
Source: blueprint sk-def-sfb-dc-setting, used in sk-prop-int-brown-construction
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev Spaces :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of k)) =>
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- Quasi-compact compactifications, precisely the recorded Nagata datum.
Source: blueprint sk-prop-int-brown-construction, second paragraph
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev Compactifications {X Y : Spaces k} (f : X ⟶ Y) :=
  Compactification.QuasiCompactObjects f.hom.left

/-- The source inclusion followed by the actual compactification composite. The
codomain is displayed in the ambient category; preservation below is what restricts it.
Source: blueprint sk-prop-int-brown-construction, displayed functor
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev candidate {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f) :=
  (localizing Λ X.obj.left).ι ⋙ image Λ c.obj

/-- Pull back the specified compactification. Quasi-compactness of its open immersion
is transported by the recorded pullback square, rather than assumed afresh.
Source: blueprint sk-prop-int-brown-construction, base-change clause
(blueprint: proposition-construction-independence-rf-shriek). -/
def baseCompactification {X Y X' Y' : Spaces k}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactifications k f)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left) :
    Compactifications k f' :=
  ⟨c.obj.ofIsPullback sq,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (c.obj.isPullback_i_ofIsPullback sq) c.property⟩

/-- The four preservation clauses. Exactness is stated by the ambient distinguished
triangles with all three vertices in Loc. Coproduct preservation means preserving every
ordinary ambient coproduct cocone on objects in Loc, in the indexing universe of the
recorded localizing closure. The last clause is preservation of the specified Dbc.
Source: blueprint sk-prop-int-brown-construction, displayed functor and next sentence
(blueprint: proposition-construction-independence-rf-shriek). -/
structure Preservation : Prop where
  maps_localizing : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), localizing Λ X.obj.left K →
      localizing Λ Y.obj.left ((image Λ c.obj).obj K)
  exact : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (T : Pretriangulated.Triangle (Ambient Λ X.obj.left)),
      localizing Λ X.obj.left T.obj₁ → localizing Λ X.obj.left T.obj₂ →
      localizing Λ X.obj.left T.obj₃ →
      T ∈ distTriang (Ambient Λ X.obj.left) →
        (image Λ c.obj).mapTriangle.obj T ∈
          distTriang (Ambient Λ Y.obj.left)
  coproducts : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (I : Type (u + 2)) (F : Discrete I ⥤ Ambient Λ X.obj.left),
      (∀ i : I, localizing Λ X.obj.left (F.obj (Discrete.mk i))) →
        PreservesColimit F (image Λ c.obj)
  maps_constructible : ∀ {X Y : Spaces k} {f : X ⟶ Y} (c : Compactifications k f)
    (K : Ambient Λ X.obj.left), generators Λ X.obj.left K →
      generators Λ Y.obj.left ((image Λ c.obj).obj K)

/-- Natural comparison maps on Loc for all pairs of compactifications.
Source: blueprint sk-prop-int-brown-construction, independence clause
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev Comparisons :=
  ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f),
    candidate Λ k c ≅ candidate Λ k d

/-- Natural composition isomorphisms, for any choices for f, g and gf. Compatibility
with the compactification comparisons is required in `Coherence`.
Source: blueprint sk-prop-int-brown-construction, composition clause
(blueprint: proposition-construction-independence-rf-shriek). -/
abbrev Compositions :=
  ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactifications k f) (d : Compactifications k g)
    (e : Compactifications k (f ≫ g)),
      candidate Λ k c ⋙ image Λ d.obj ≅ candidate Λ k e

/-- Canonicity, identity, cocycle, composition and base-change compatibility for the
specified module-object compact-support functors. Normalization on a boundary refinement
uses the actual proper counit and open unit. The base-change map is the specified mate,
not an arbitrary isomorphism with the right source and target.

All maps are natural transformations on full subcategories of the same ambient derived
categories. Preservation of generators and of pullback, recorded in `constructible_pull`,
therefore restricts these very same maps and equations to Dbc.

Source: blueprint sk-prop-int-brown-construction, last three sentences
(blueprint: proposition-construction-independence-rf-shriek). -/
structure Coherence (h : Preservation Λ k) (φ : Comparisons Λ k)
    (μ : Compositions Λ k) : Prop where
  identity : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _
  cocycle : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e
  normalized : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e
  composition_compatibility : ∀ {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : Compactifications k f) (d d' : Compactifications k g)
    (e e' : Compactifications k (f ≫ g))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (image Λ d.obj).map ((φ f c c').hom.app K) ≫
          (φ g d d').hom.app
            ⟨(image Λ c'.obj).obj K.obj, h.maps_localizing c' K.obj K.property⟩ ≫
          (μ f g c' d' e').hom.app K =
        (μ f g c d e).hom.app K ≫ (φ (f ≫ g) e e').hom.app K
  constructible_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    generators Λ Y.obj.left K →
      generators Λ X.obj.left ((pull Λ v.hom.left).obj K)
  localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    localizing Λ Y.obj.left K →
      localizing Λ X.obj.left ((pull Λ v.hom.left).obj K)
  base_change : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f),
      ∃ ho : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq),
        ∀ K : (localizing Λ X.obj.left).FullSubcategory,
          IsIso ((baseChange Λ c.obj sq ho).app K.obj)
  base_change_compatibility : ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f)
    (hc : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (pull Λ v.hom.left).map ((φ f c d).hom.app K) ≫
          (baseChange Λ d.obj sq hd).app K.obj =
        (baseChange Λ c.obj sq hc).app K.obj ≫
          (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
            ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u' K.obj K.property⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
