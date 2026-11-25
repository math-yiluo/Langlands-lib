/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Induced topological cohomology map and terminal generator map

Source: Stacks Project, Cohomology of Sheaves, Sections 01DZ and 20.13 (Tag 01F2).
The cohomology transformation is constructed using the exact inverse-image functor on Ext.
(blueprint: lem-sc-topological-induced-edge-and-map)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace CategoryTheory

private noncomputable def sectionEquiv
    {C : Type*} [Category.{u} C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] (U : C) (M : Sheaf T AddCommGrpCat.{u}) :
    ((presheafToSheaf T AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ M) ≃ M.obj.obj (op U) :=
  ((sheafificationAdjunction T AddCommGrpCat.{u}).homEquiv _ M).trans
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj U) M.obj).trans
      yonedaEquiv)

-- The existing existential binder `edge` is intentionally unconstrained in the conclusion.
set_option linter.unusedVariables false in
/-- A continuous map induces a natural map from direct-image cohomology to source cohomology,
and a terminal free abelian sheaf map with the inverse-image generator rule.

Source: Stacks Project, Cohomology of Sheaves, Section 01DZ and the exact inverse-image
adjunction used in Section 20.13 (Tag 01F2).
(blueprint: lem-sc-topological-induced-edge-and-map)

Proof: Write KX and KZ for the sheafified free terminal representables. The sheafification,
free-forgetful and Yoneda adjunctions identify maps from these objects with terminal sections.
For the exact inverse-image functor L, take the image of the universal generator of KX under
its adjunction unit. Since the inverse image of the terminal open is terminal, this is a
terminal section of L(KX); the preceding representation constructs b:KZ -> L(KX).
Apply L to Ext(KX, f_*F), precompose with b, and postcompose with the adjunction counit
L(f_*F) -> F. Ext associativity and counit naturality prove naturality in F.
For a:KX -> f_*KZ, first map each representable generator to its inverse image composed with
the terminal-open equality, extend by the free abelian functor, and compose with sheafification
on Z. The sheafification lifting property on X constructs a and proves its generator formula.
Finally transport the cohomology functors using hX and hZ.
-/
theorem exists_topological_induced_edge_and_map
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
                eqToHom (Opens.map_top f)))) := by
  have hHX := funext hX
  have hHZ := funext hZ
  rw [hHX, hHZ]
  let TX := Opens.grothendieckTopology X
  let TZ := Opens.grothendieckTopology Z
  let KX := (presheafToSheaf TX AddCommGrpCat.{u}).obj
    (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)
  let KZ := (presheafToSheaf TZ AddCommGrpCat.{u}).obj
    (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)
  let P := TopCat.Sheaf.pushforwardAb f
  let L := Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
    AddCommGrpCat.{u} TX TZ
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    AddCommGrpCat.{u} TX TZ
  have : L.Additive := adj.left_adjoint_additive
  have := adj.leftAdjoint_preservesColimits
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map f)
  have : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback _ _ _ _
  let t := (toSheafify TX (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
    (op ⊤) (FreeAbelianGroup.of (𝟙 (⊤ : Opens X)))
  let b : KZ ⟶ L.obj KX := (sectionEquiv TZ ⊤ (L.obj KX)).symm
    ((L.obj KX).obj.map (eqToHom (Opens.map_top f).symm).op
      ((adj.unit.app KX).hom.app (op ⊤) t))
  let edge : ∀ p : ℕ,
      P ⋙ Sheaf.cohomologyPresheafFunctor TX p ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⟶
      Sheaf.cohomologyPresheafFunctor TZ p ⋙
        (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) := fun p ↦
    { app := fun F ↦ AddCommGrpCat.ofHom
          (((Abelian.Ext.mk₀ (adj.counit.app F)).postcomp KZ (add_zero p)).comp
            (((Abelian.Ext.mk₀ b).precomp (L.obj (P.obj F)) (zero_add p)).comp
              (L.mapExtAddHom KX (P.obj F) p)))
      naturality := by
        intro F G g
        ext e
        change Abelian.Ext KX (P.obj F) p at e
        change ((Abelian.Ext.mk₀ b).comp
          ((e.comp (Abelian.Ext.mk₀ (P.map g)) (add_zero p)).mapExactFunctor L)
          (zero_add p)).comp (Abelian.Ext.mk₀ (adj.counit.app G)) (add_zero p) =
          (((Abelian.Ext.mk₀ b).comp (e.mapExactFunctor L) (zero_add p)).comp
            (Abelian.Ext.mk₀ (adj.counit.app F)) (add_zero p)).comp
              (Abelian.Ext.mk₀ g) (add_zero p)
        simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
        simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
          Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
        have hg : L.map (P.map g) ≫ adj.counit.app G = adj.counit.app F ≫ g :=
          adj.counit.naturality g
        rw [hg] }
  let τ : yoneda.obj (⊤ : Opens X) ⟶ (Opens.map f).op ⋙ yoneda.obj (⊤ : Opens Z) :=
    { app := fun U ↦ TypeCat.ofHom (fun h ↦ (Opens.map f).map h ≫
        eqToHom (Opens.map_top f))
      naturality := by
        intro U V i
        ext h
        dsimp
        apply Subsingleton.elim }
  let η : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ⟶ (P.obj KZ).obj :=
    Functor.whiskerRight τ AddCommGrpCat.free ≫
      Functor.whiskerLeft (Opens.map f).op
        (toSheafify TZ (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free))
  let a : KX ⟶ P.obj KZ := ⟨sheafifyLift TX η (P.obj KZ).property⟩
  refine ⟨edge, a, ?_⟩
  intro U h
  have ha := congrArg (fun e ↦ e.app (op U))
    (toSheafify_sheafifyLift TX η (P.obj KZ).property)
  have ha' := congrArg (fun e ↦ e (FreeAbelianGroup.of h)) ha
  change (sheafifyLift TX η (P.obj KZ).property).app (op U)
    ((toSheafify TX (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
      (op U) (FreeAbelianGroup.of h)) = _
  change (sheafifyLift TX η (P.obj KZ).property).app (op U)
    ((toSheafify TX (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
      (op U) (FreeAbelianGroup.of h)) = η.app (op U) (FreeAbelianGroup.of h) at ha'
  rw [ha']
  simp [η, τ, AddCommGrpCat.free_map]
  rfl

end CategoryTheory
