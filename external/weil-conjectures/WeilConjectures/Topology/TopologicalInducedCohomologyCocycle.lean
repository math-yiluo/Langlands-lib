/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.Topology.TopologicalInducedEdgeAndMap
import WeilConjectures.Topology.TopologicalInducedCocycleFormula

/-! # The induced topological cohomology map on cocycles -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- The map induced by a continuous map on cohomology of its direct image, described on
arbitrary injective-resolution cocycles. This statement involves no spectral sequence.

Source: Stacks Project, Cohomology of Sheaves, Section 20.2 (Tag 01DZ), the composition
comparison in Section 20.13 (Tag 01F2), and the resolution definition of the induced map.
(blueprint: lem-sc-topological-induced-cohomology-cocycle)

Proof: Let KX and KZ be the free abelian terminal sheaves in the displayed formula.
The inverse-image/direct-image adjunction identifies inverse image of KX with KZ:
both represent global sections after the sectionwise equality of sections over terminal
opens. The adjunction unit gives a : KX -> f_*KZ. On the sheafification generators it
sends h to the inverse-image arrow composed with the equality f^{-1}(X)=Z, giving the
first equation. This description determines a, since generators determine a presheaf
map and the sheafification adjunction determines its extension.

The inverse-image functor is exact. Apply its derived functor to Ext(KX,f_*F), then
precompose with the preceding identification and postcompose with the derived counit
to obtain Ext(KZ,F). The resulting homomorphisms are natural in F, hence assemble into
edge. Equivalently compute them on injective resolutions: comparison J -> f_*I over
F followed by the sectionwise terminal-sections identification gives the map on
cohomology. Any two comparisons over F are homotopic; their global-section maps are
homotopic, so the map is independent of comparisons and resolutions. For a cocycle s,
the equation a >> f_*z = s >> phi says that this comparison sends s precisely to z.
The Ext computation of cohomology by I.extMk and J.extMk therefore gives the displayed
second equation. Transport it along hX and hZ. Boundaries go to boundaries by the
chain-map equation. In degree zero this is the ordinary map on global sections;
for the identity map it is the identity, and for the zero sheaf both groups vanish.
-/
theorem exists_topological_induced_cohomology_cocycle
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) :
    ∃ edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p,
      ∃ a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)),
      (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f)))) ∧
      (∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (_hφ : J.ι.f 0 ≫ φ.f 0 =
          (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ)
        (s : (presheafToSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
            J.cocomplex.X p)
        (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
        (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
            I.cocomplex.X p)
        (hz : z ≫ I.cocomplex.d p (p + 1) = 0)
        (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        (eqToHom (congrArg (fun Q ↦ Q.obj F) (hZ p)))
          ((edge p).app F
            ((eqToHom (congrArg (fun Q ↦ Q.obj
              ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
              (J.extMk s (p + 1) rfl hs))) =
            I.extMk z (p + 1) rfl hz) := by
  obtain ⟨_, a, ha⟩ :=
    exists_topological_induced_edge_and_map f HX HZ hX hZ
  obtain ⟨edge, hedge⟩ := topological_induced_cocycle_formula f HX HZ hX hZ a ha
  exact ⟨edge, a, ha, hedge⟩

end CategoryTheory
