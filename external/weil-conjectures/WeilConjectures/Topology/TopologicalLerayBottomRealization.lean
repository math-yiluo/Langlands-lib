/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.Topology.TopologicalLerayCartanEilenbergCocycle
import WeilConjectures.Topology.TopologicalResolutionCocycleLift

/-! # Realization of the canonical Leray bottom edge -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

private theorem eqToHom_apply_injective {A B : AddCommGrpCat.{u}} (h : A = B) :
    Function.Injective (eqToHom h) := by
  subst B
  exact fun _ _ h ↦ h

private theorem eqToHom_apply_symm {A B : AddCommGrpCat.{u}} (h : A = B) (x : A) :
    (eqToHom h.symm) ((eqToHom h) x) = x := by
  subst B
  rfl

private theorem topological_cohomology_edge_eq_of_cocycles
    {Z X : TopCat.{u}} (f : Z ⟶ X)
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (edge bottom : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p)
    (h : ∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
      (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F)) (p : ℕ)
      (s : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ J.cocomplex.X p)
      (hs : s ≫ J.cocomplex.d p (p + 1) = 0),
      (edge p).app F
          ((eqToHom (congrArg (fun Q ↦ Q.obj
            ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
            (J.extMk s (p + 1) rfl hs)) =
        (bottom p).app F
          ((eqToHom (congrArg (fun Q ↦ Q.obj
            ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
            (J.extMk s (p + 1) rfl hs))) : edge = bottom := by
  funext p
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro x
  let J := injectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F)
  let α := (eqToHom (congrArg (fun Q ↦ Q.obj
    ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p))) x
  obtain ⟨s, hs, hclass⟩ := J.extMk_surjective α (p + 1) rfl
  have input : (eqToHom (congrArg (fun Q ↦ Q.obj
      ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
        (J.extMk s (p + 1) rfl hs) = x := by
    rw [hclass]
    exact eqToHom_apply_symm _ x
  simpa only [input] using h F J p s hs

/-- Realize a cohomology map already characterized on resolution cocycles as the bottom
edge of a functorial Leray spectral sequence. The induced map and its cocycle computation
are inputs; this statement constructs only the spectral sequence and its finite filtration.

Source: Stacks Project, Cohomology Lemma 01F2, and Derived Categories Lemma 015N, with
its Cartan--Eilenberg construction and finite-filtration conclusion.
(blueprint: lem-sc-topological-leray-bottom-realization)

Proof: Apply the Grothendieck spectral-sequence construction to f_* and global sections
on X. Direct image is left exact sectionwise and additive by hypothesis. It sends
injectives to injectives by topological pushforward injectivity, hence to
sections-acyclics. Abelian sheaves are Grothendieck abelian categories with enough
injectives. Global sections after f_* agrees with global sections on Z. The canonical
resolution computation therefore identifies the second page with R^b f_* followed by
HX a and the abutment with HZ n, transported through hX and hZ.

Construct the pages in the functor category using natural resolution comparisons;
comparison homotopies induce the same maps from page two onward. The second filtration
on the Cartan--Eilenberg total complex gives T; its image filtration has top at zero
and bottom at n+1. Its graded quotients give g. In the first quadrant, both differentials
at (p,q) vanish for r > max(p,q+1), giving stabilization at page p+q+2.
On the bottom row the outgoing differential vanishes. The cycles inclusion is therefore
an isomorphism; compose its inverse with homology projection and the next-page
isomorphism to obtain t, with the displayed equation. Start b at the identity and
iterate t. Since the final filtration step T(p).step(p+1) vanishes, its cokernel quotient
identifies with T(p).step p; invert g p 0 through that identification to obtain k.

The resulting bottom map sends a resolution cocycle s to the global cocycle obtained
by the resolution comparison J -> f_*I, as follows by the augmentation into the
resolution-degree-zero summands of the total complex. This global cocycle is a unique
z under the representation of sections by the free terminal sheaf, and satisfies hz
and a >> f_*z = s >> phi. The assumed cocycle formula identifies its class with edge.
Every cohomology class is J.extMk of a cocycle. Thus this equality on cocycles implies
equality of morphisms in every sheaf, hence the displayed natural-transformation
factorization. For p=0, b at page two is the identity; for f the identity this specializes
to the one-row sequence. No acyclicity assumption on the original sheaf is introduced.
-/
theorem exists_topological_leray_bottom_realization
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p)
    (a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)))
    (ha : (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f)))))
    (hedge : (∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
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
            I.extMk z (p + 1) rfl hz)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat
        (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}),
      ∃ e₂ : ∀ a b : ℕ, (E.page 2).X (a, b) ≅
          (TopCat.Sheaf.pushforwardAb f).rightDerived b ⋙ HX a,
        (∀ a b : ℕ, ∃ (R : ℤ) (_hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          Nonempty ((E.page r (by omega)).X (a, b) ≅ E.pageInfinity (a, b))) ∧
        ∃ T : ∀ n : ℕ, DecreasingFiltration (HZ n),
          (∀ n, (T n).step 0 = ⊤) ∧
          (∀ n, (T n).step (n + 1) = ⊥) ∧
          ∃ g : ∀ p q : ℕ, (T (p + q)).gradedPiece p ≅ E.pageInfinity (p, q),
            ∃ e₀ : ∀ p : ℕ,
                TopCat.Sheaf.pushforwardAb f ⋙ HX p ≅ (E.page 2).X (p, 0),
              (∀ p, (e₀ p).hom =
                Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero
                  (HX p) ≫ (e₂ p 0).inv) ∧
              ∃ t : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                  (E.page r hr).X (p, 0) ⟶ (E.page (r + 1) (by omega)).X (p, 0),
                (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                  (E.page r hr).iCycles (p, 0) ≫ t p r hr =
                    (E.page r hr).homologyπ (p, 0) ≫ (E.iso r (r + 1) (p, 0) rfl hr).hom) ∧
                ∃ b : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                    (E.page 2).X (p, 0) ⟶ (E.page r hr).X (p, 0),
                  (∀ p, b p 2 (by omega) = 𝟙 _) ∧
                  (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                    b p (r + 1) (by omega) = b p r hr ≫ t p r hr) ∧
                  ∃ k : ∀ p : ℕ, E.pageInfinity (p, 0) ≅ ((T p).step p :
                      Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
                        AddCommGrpCat.{u}),
                    (∀ p, cokernel.π (Subobject.ofLE ((T p).step (p + 1))
                      ((T p).step p) ((T p).antitone_step (by omega))) ≫
                        (g p 0).hom = (k p).inv) ∧
                    (∀ p, edge p = (e₀ p).hom ≫ b p (p + 2) (by omega) ≫
                      (k p).hom ≫ ((T p).step p).arrow) := by
  refine Exists.imp (fun E ↦ ?_)
    (exists_topological_leray_cartan_eilenberg_cocycle f HX HZ hX hZ a ha)
  refine Exists.imp (fun e₂ ↦ ?_)
  refine And.imp_right ?_
  refine Exists.imp (fun T ↦ ?_)
  refine And.imp_right ?_
  refine And.imp_right ?_
  refine Exists.imp (fun g ↦ ?_)
  refine Exists.imp (fun e₀ ↦ ?_)
  refine And.imp_right ?_
  refine Exists.imp (fun t ↦ ?_)
  refine And.imp_right ?_
  refine Exists.imp (fun b ↦ ?_)
  refine And.imp_right ?_
  refine And.imp_right ?_
  refine Exists.imp (fun k ↦ ?_)
  refine And.imp_right ?_
  rintro ⟨bottom, hbottom, computation⟩
  have h : edge = bottom := topological_cohomology_edge_eq_of_cocycles f HX HZ hX
    edge bottom (by
      intro F J p s hs
      let I := injectiveResolution F
      obtain ⟨φ, hφ, z, hz, hsz⟩ :=
        exists_topological_resolution_cocycle_lift f a ha F I J p s hs
      exact eqToHom_apply_injective _
        ((hedge F I J φ hφ p s hs z hz hsz).trans
          (computation F I J φ hφ p s hs z hz hsz).symm))
  exact fun p ↦ (congrFun h p).trans (hbottom p)

end CategoryTheory
