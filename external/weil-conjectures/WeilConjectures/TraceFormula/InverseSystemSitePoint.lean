/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Inverse-system site points

Source: Stacks Project, Sites, Tags 00YC and 00YA, with the inverse-system
construction in Tag 00YQ (auxiliary; not a blueprint node).

The inverse system is represented by a functor from the opposite of a directed
poset.  Its colimit of representables is the functor `inverseSystemHomFunctor`,
and the colimit of sections along it is the functor
`inverseSystemSectionColimitFunctor`.  The site is a precoverage, with sheaves for the
generated Grothendieck topology, as in the dependency def-weil-pbc-sites-and-cohomology;
the construction does not need the site axioms `Precoverage.IsSiteForCoverings`.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The opposite-category diagram of objects in an inverse system.
Source: Stacks Project, Sites, Tag 00YQ (auxiliary; not a blueprint node). -/
def inverseSystemOppositeDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : I ⥤ Cᵒᵖ where
  obj i := op (U.obj (op i))
  map {X Y} f := (U.map f.op).op
  map_id i := by simp
  map_comp f g := by simp

/-- The diagram of representable functors obtained from an inverse system.
Source: Stacks Project, Sites, Tags 00YC and 00YQ
(auxiliary; not a blueprint node). -/
def inverseSystemRepresentableDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : I ⥤ (C ⥤ Type u) where
  obj i := coyoneda.obj (op (U.obj (op i)))
  map {X Y} f := coyoneda.map (U.map f.op).op
  map_id i := by simp
  map_comp f g := by simp

/-- The colimit of representables attached to an inverse system,
`u(W) = colim_i Hom(U_i, W)`.
Source: Stacks Project, Sites, Tags 00YC and 00YQ
(auxiliary; not a blueprint node). -/
noncomputable def inverseSystemHomFunctor {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : C ⥤ Type u :=
  colimit (inverseSystemRepresentableDiagram U)

/-- The section diagram `i ↦ F(U_i)` of a sheaf along an inverse system.
Source: Stacks Project, Sites, Tags 00YA and 00YQ
(auxiliary; not a blueprint node). -/
def inverseSystemSectionDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] {J : GrothendieckTopology C}
    (U : Iᵒᵖ ⥤ C) (F : Sheaf J (Type w)) : I ⥤ Type w :=
  inverseSystemOppositeDiagram U ⋙ ObjectProperty.FullSubcategory.obj F

/-- The functor `F ↦ colim_i F(U_i)` on sheaves of sets, acting on a morphism of
sheaves by its section maps at the `U_i`; its value at `F` is the colimit of
`inverseSystemSectionDiagram U F`.
Source: Stacks Project, Sites, Tags 00YA and 00YQ
(auxiliary; not a blueprint node). -/
noncomputable def inverseSystemSectionColimitFunctor {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (J : GrothendieckTopology C) (U : Iᵒᵖ ⥤ C) :
    Sheaf J (Type (max u w)) ⥤ Type (max u w) :=
  sheafToPresheaf J (Type (max u w)) ⋙
    (Functor.whiskeringLeft I Cᵒᵖ (Type (max u w))).obj (inverseSystemOppositeDiagram U) ⋙
      colim

private theorem hom_preservesFiniteLimits {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C) : PreservesFiniteLimits (inverseSystemHomFunctor U) := by
  exact ObjectProperty.preservesFiniteLimits.prop_colimit
    (inverseSystemRepresentableDiagram U) (fun i ↦ by
      change PreservesFiniteLimits (coyoneda.obj (op (U.obj (op i))))
      infer_instance)

private noncomputable def homMk {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) {i : I} {X : C}
    (f : U.obj (op i) ⟶ X) : (inverseSystemHomFunctor U).obj X :=
  (colimit.ι (inverseSystemRepresentableDiagram U) i).app X f

private theorem homMk_surjective {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) {X : C}
    (x : (inverseSystemHomFunctor U).obj X) :
    ∃ (i : I) (f : U.obj (op i) ⟶ X), homMk U f = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation C (Type u)).obj X)
      (colimit.isColimit (inverseSystemRepresentableDiagram U))) x

private theorem homMk_map {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) {i : I} {X Y : C}
    (f : U.obj (op i) ⟶ X) (g : X ⟶ Y) :
    (inverseSystemHomFunctor U).map g (homMk U f) = homMk U (f ≫ g) := by
  exact (ConcreteCategory.congr_hom
    ((colimit.ι (inverseSystemRepresentableDiagram U) i).naturality g) f).symm

private theorem homMk_transition {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) {i j : I}
    (q : j ⟶ i) {X : C} (f : U.obj (op j) ⟶ X) :
    homMk U (U.map q.op ≫ f) = homMk U f := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (colimit.w (inverseSystemRepresentableDiagram U) q) X) f

private theorem homMk_eq {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C) {i : I} {X : C} {f g : U.obj (op i) ⟶ X}
    (h : homMk U f = homMk U g) :
    ∃ (j : I) (q : i ⟶ j), U.map q.op ≫ f = U.map q.op ≫ g := by
  exact (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation C (Type u)).obj X)
      (colimit.isColimit (inverseSystemRepresentableDiagram U))) f g).1 h

private theorem lift_saturated {C : Type u} [Category.{u} C]
    (F : C ⥤ Type u) [IsCofiltered F.Elements] (J : Precoverage C)
    (h : ∀ (X : C) (R : Presieve X), R ∈ J X → ∀ x : F.obj X,
      ∃ (Y : C) (f : Y ⟶ X), R f ∧ ∃ y : F.obj Y, F.map f y = x)
    {X : C} (R : Sieve X) (hR : R ∈ J.toGrothendieck X) :
    ∀ x : F.obj X, ∃ (Y : C) (f : Y ⟶ X), R f ∧ ∃ y : F.obj Y, F.map f y = x := by
  induction hR with
  | of X S hS =>
    intro x
    obtain ⟨Y, f, hf, y, hy⟩ := h X S hS x
    exact ⟨Y, f, Sieve.le_generate S Y f hf, y, hy⟩
  | top X =>
    intro x
    exact ⟨X, 𝟙 X, trivial, x, by simp⟩
  | pullback X S hS Y f ih =>
    intro y
    obtain ⟨Z, g, hg, z, hz⟩ := ih (F.map f y)
    let a : F.elementsMk Z z ⟶ F.elementsMk X (F.map f y) := ⟨g, hz⟩
    let b : F.elementsMk Y y ⟶ F.elementsMk X (F.map f y) := ⟨f, rfl⟩
    obtain ⟨T, p, q, _⟩ := IsCofilteredOrEmpty.cone_objs (F.elementsMk Z z) (F.elementsMk Y y)
    obtain ⟨V, r, hr⟩ := IsCofilteredOrEmpty.cone_maps (p ≫ a) (q ≫ b)
    refine ⟨V.1, r.1 ≫ q.1, ?_, V.2, ?_⟩
    · change S ((r.1 ≫ q.1) ≫ f)
      have eq := congrArg (fun t ↦ t.1) hr
      change r.1 ≫ (p.1 ≫ g) = r.1 ≫ (q.1 ≫ f) at eq
      rw [Category.assoc, ← eq, ← Category.assoc]
      exact S.downward_closed hg _
    · exact (r ≫ q).2
  | transitive X S R hS hR ihS ihR =>
    intro x
    obtain ⟨Y, f, hf, y, hy⟩ := ihS x
    obtain ⟨Z, g, hg, z, hz⟩ := ihR hf y
    refine ⟨Z, g ≫ f, hg, z, ?_⟩
    simp [Functor.map_comp, ← hy, ← hz]

private noncomputable def systemElements {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) :
    Iᵒᵖ ⥤ (inverseSystemHomFunctor U).Elements where
  obj i := (inverseSystemHomFunctor U).elementsMk (U.obj i) (homMk U (𝟙 _))
  map {i j} q := ⟨U.map q, by
    rw [homMk_map]
    simpa using homMk_transition U q.unop (𝟙 _)⟩

private theorem systemElements_initial {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C) : (systemElements U).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨x⟩
    obtain ⟨i, f, rfl⟩ := homMk_surjective U x
    exact ⟨op i, ⟨f, by simp [systemElements, homMk_map]⟩⟩
  · rintro ⟨x⟩ i ⟨f, hf⟩ ⟨g, hg⟩
    obtain ⟨j, q, hq⟩ := homMk_eq U
      (f := f) (g := g) (by simpa [systemElements, homMk_map] using hf.trans hg.symm)
    exact ⟨op j, q.op, by ext; exact hq⟩

private noncomputable def stalkComparison {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C) {J : GrothendieckTopology C}
    (p : J.Point) (hp : p.fiber = inverseSystemHomFunctor U) :
    p.sheafFiber (A := Type (max u w)) ≅ inverseSystemSectionColimitFunctor J U := by
  rcases p with ⟨F, hF, hs, hl⟩
  dsimp at hp
  subst F
  have := systemElements_initial U
  let T := (opOpEquivalence I).inverse ⋙ (systemElements U).op
  have : T.Final := inferInstance
  exact Functor.isoWhiskerLeft (sheafToPresheaf J (Type (max u w)))
    (Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ _).obj (Functor.Elements.π (inverseSystemHomFunctor U)).op)
      (Functor.Final.colimIso T)).symm

/-- Inverse-system criterion for a point of a small site.
Source: Stacks Project, Sites, Tags 00YC (Proposition proposition-point-limits),
00YA (Lemma lemma-point-site-topos), and 00YQ (Proposition proposition-criterion-points)
(auxiliary; not a blueprint node).

Proof sketch (the node's steps):
1. A directed colimit of sets is the quotient of the pairs `(i, a)` by eventual
   equality at a common later index; every class has a representative.
2. `u(h)[i, a] = [i, h ∘ a]` is a functor; `Hom(U_i, -)` preserves finite limits and
   filtered colimits commute with finite limits in sets, so `u` preserves finite limits.
3. `S(F) = colim_i F(U_i)` preserves finite limits: finite limits of sheaves are
   computed sectionwise, and the same commutation applies.
4. The covering hypothesis is joint surjectivity; an empty covering forces `u(W)` empty.
5. The functor `i ↦ (U_i, [i, id])` to the neighbourhood category is initial:
   representatives provide arrows to every neighbourhood, and eventual equality
   equalizes parallel such arrows. Its opposite computes the neighbourhood stalk
   `T(F)` as `S(F)`, naturally in `F`, by Mathlib's `Functor.Final.colimIso`.
6. Finite-limit preservation makes the category of elements cofiltered. The
   covering-lifting property extends to the generated topology by induction on
   saturation: cofiltered cones and equalizers handle pullbacks, and successive
   lifts handle transitivity. This constructs a Mathlib site point with fibre `u`.
7. Mathlib's `Point.skyscraperSheafFunctor` supplies the sheaf
   `R(E)(W) = Map(u(W), E)` and `Point.skyscraperSheafAdjunction` gives `T ⊣ R`.
8. Transport this adjunction across `T ≅ S`. With step 3 this is a geometric
   morphism `Set → Sh(C)` whose inverse image is exactly `S`.
-/
theorem inverseSystemSitePoint {C : Type u} [Category.{u} C]
    [HasFiniteLimits C] (J : Precoverage C)
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C)
    (hcover : ∀ {K : Type u} {W : C} (V : K → C) (a : ∀ k, V k ⟶ W),
      Presieve.ofArrows V a ∈ J W →
      ∀ f : (inverseSystemHomFunctor U).obj W,
        ∃ (k : K) (g : (inverseSystemHomFunctor U).obj (V k)),
          (inverseSystemHomFunctor U).map (a k) g = f) :
    PreservesFiniteLimits (inverseSystemHomFunctor U) ∧
      (∀ (K : Type u) (W : C) (V : K → C) (a : ∀ k, V k ⟶ W)
        (_ : Presieve.ofArrows V a ∈ J W)
        (f : (inverseSystemHomFunctor U).obj W),
        ∃ (k : K) (g : (inverseSystemHomFunctor U).obj (V k)),
          (inverseSystemHomFunctor U).map (a k) g = f) ∧
      ∃ (p : GeometricMorphism (Type (max u w))
          (Sheaf J.toGrothendieck (Type (max u w)))),
        Nonempty (p.inverse ≅ inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U) := by
  have hlim := hom_preservesFiniteLimits U
  have := (inverseSystemHomFunctor U).isCofiltered_elements
  have hpre : ∀ (X : C) (R : Presieve X), R ∈ J X →
      ∀ x : (inverseSystemHomFunctor U).obj X,
        ∃ (Y : C) (f : Y ⟶ X), R f ∧
          ∃ y : (inverseSystemHomFunctor U).obj Y,
            (inverseSystemHomFunctor U).map f y = x := by
    intro X R hR x
    obtain ⟨K, V, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨k, y, hy⟩ := hcover V a hR x
    exact ⟨V k, a k, ⟨k⟩, y, hy⟩
  have := systemElements_initial U
  have : InitiallySmall.{u} (inverseSystemHomFunctor U).Elements :=
    initiallySmall_of_initial_of_essentiallySmall (systemElements U)
  let p : J.toGrothendieck.Point :=
    { fiber := inverseSystemHomFunctor U
      jointly_surjective R hR x := by
        obtain ⟨Y, f, hf, y, hy⟩ := lift_saturated _ J hpre R hR x
        exact ⟨Y, f, hf, y, hy⟩ }
  refine ⟨hlim, fun K W V a ha f ↦ hcover V a ha f, ?_⟩
  refine ⟨{ inverse := inverseSystemSectionColimitFunctor J.toGrothendieck U
            direct := p.skyscraperSheafFunctor
            adj := p.skyscraperSheafAdjunction.ofNatIsoLeft (stalkComparison U p rfl)
            leftExact := ?_ }, ?_⟩
  · unfold inverseSystemSectionColimitFunctor
    infer_instance
  · exact ⟨Iso.refl _⟩

end CategoryTheory
