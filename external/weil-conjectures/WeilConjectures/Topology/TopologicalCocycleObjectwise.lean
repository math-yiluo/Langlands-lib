/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.Topology.TopologicalLeraySpectralObjectAugmentation

/-! # Objectwise topological cocycle comparison -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace CategoryTheory
set_option linter.unusedVariables false in
/-- Objectwise additive maps on canonical cohomology, independent of comparisons.
Source: Stacks Project, Cohomology, Section 20.2 (Tag 01DZ); Derived Categories,
Section 13.18, Lemmas 13.18.6 and 13.18.7 (comparison and homotopy uniqueness).
(blueprint: lem-sc-topological-cocycle-objectwise)

Proof: Direct image preserves injectives since its left adjoint is exact. Choose an
injective resolution of F and of f_*F and extend the identity on f_*F to a comparison
into f_*I. Apply global sections and the terminal-sections identification represented
by a. Chain maps preserve cycles and boundaries, so this gives an additive map on
cohomology. The Ext computation identifies this map with the displayed homomorphism.
Any other pair of resolutions is linked to the chosen pair by comparison maps over
identity maps. Comparisons into a bounded-below complex of injectives are homotopic;
thus the resulting cohomology map is independent of resolutions and comparisons.
The free/sheafification/Yoneda adjunction identifies Hom(KX,G) with G(X),
and Hom(KZ,T) with T(Z). Under these identifications, the generator condition
on a says that z maps to the same terminal section through f_*. Consequently
z maps to a >> f_*z by a bijection natural in T. In each degree this identifies
the two global-section complexes, including their differentials. Thus every
image of a source cycle has a unique z, which is a cycle; boundaries correspond
as well. This also shows that the displayed property uniquely determines tau,
since every Ext class is represented by s and each s has such a z. Hence a >> f_*z = s >> phi
gives the stated equality of Ext classes.
Zero sheaves and zero cocycles give zero, degree zero gives ordinary sections, and
for an identity continuous map this construction gives the identity.
-/
theorem exists_topological_cocycle_objectwise
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)))
    (ha : ∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f))))
    (p : ℕ) (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    ∃ τ : (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj
        ((TopCat.Sheaf.pushforwardAb f).obj F) ⟶
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj F,
      ∀
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (hφ : J.ι.f 0 ≫ φ.f 0 =
          (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0))
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
        (hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        τ (J.extMk s (p + 1) rfl hs) = I.extMk z (p + 1) rfl hz := by
  let HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u}) := fun n => Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u}) := fun n => Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology Z) n ⋙
          (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  have hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) := fun _ => rfl
  have hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology Z) n ⋙
        (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) := fun _ => rfl
  obtain ⟨Y, hY, h, e, he⟩ :=
    exists_topological_leray_spectral_object_augmentation f HX HZ hX hZ a ha
  refine ⟨(Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero (HX p) ≫
    (e p 0).inv ≫ @Abelian.SpectralObject.bottomEdge _ _ _ Y hY p ≫ (h p).hom).app F, ?_⟩
  intro I J φ hφ s hs z hz hsz
  simpa [HX, HZ] using he F I J φ hφ p s hs z hz hsz

end CategoryTheory
