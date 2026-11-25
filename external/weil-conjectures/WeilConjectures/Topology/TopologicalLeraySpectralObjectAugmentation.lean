/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import WeilConjectures.CategoryTheory.GrothendieckBottomResolutionComparison
import WeilConjectures.Topology.TopologicalTerminalResolutionExtComparison

/-! # The topological Leray spectral object and its augmentation

Source: Stacks Project, Tags 015N, 015J and 01F2.
(blueprint: lem-sc-topological-leray-spectral-object-augmentation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ComposableArrows

namespace CategoryTheory

private theorem exact_of_evaluation
    {A C : Type*} [Category A] [Category C] [Abelian C]
    (S : ShortComplex (A ⥤ C))
    (h : ∀ X, (S.map ((evaluation A C).obj X)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro X
  exact ((S.mapHomologyIso ((evaluation A C).obj X)).isZero_iff).1
    (((S.map ((evaluation A C).obj X)).exact_iff_isZero_homology).1 (h X))

private theorem exact_arrows_of_evaluation
    {A C : Type*} [Category A] [Category C] [Abelian C]
    {F G H : A ⥤ C} (f : F ⟶ G) (g : G ⟶ H)
    (h : ∀ X, (mk₂ (f.app X) (g.app X)).Exact) : (mk₂ f g).Exact := by
  have w : f ≫ g = 0 := by
    ext X
    exact (h X).toIsComplex.zero 0
  apply ShortComplex.Exact.exact_toComposableArrows (S := ShortComplex.mk f g w)
  apply exact_of_evaluation
  intro X
  exact (exact₂_iff _ (h X).toIsComplex).1 (h X)

private noncomputable def assembleSpectralObject
    {A C : Type*} [Category A] [Category C] [Abelian C]
    (S : A ⥤ Abelian.SpectralObject C EInt) : Abelian.SpectralObject (A ⥤ C) EInt where
  H n :=
    { obj D := S ⋙ Abelian.SpectralObject.hFunctor n D
      map α :=
        { app X := ((S.obj X).H n).map α
          naturality X Y f := (((S.map f).hom n).naturality α).symm }
      map_id D := by ext X; exact ((S.obj X).H n).map_id D
      map_comp α β := by ext X; exact ((S.obj X).H n).map_comp α β }
  δ' n₀ n₁ h :=
    { app D :=
        { app X := ((S.obj X).δ' n₀ n₁ h).app D
          naturality X Y f := by
            obtain ⟨i, j, k, a, b, rfl⟩ := mk₂_surjective D
            exact ((S.map f).comm n₀ n₁ h a b).symm }
      naturality D E α := by
        ext X
        exact ((S.obj X).δ' n₀ n₁ h).naturality α }
  exact₁' n₀ n₁ h D := by
    apply exact_arrows_of_evaluation
    intro X
    exact (S.obj X).exact₁' n₀ n₁ h D
  exact₂' n D := by
    apply exact_arrows_of_evaluation
    intro X
    exact (S.obj X).exact₂' n D
  exact₃' n₀ n₁ h D := by
    apply exact_arrows_of_evaluation
    intro X
    exact (S.obj X).exact₃' n₀ n₁ h D

private theorem assemble_firstQuadrant
    {A C : Type*} [Category A] [Category C] [Abelian C]
    (S : A ⥤ Abelian.SpectralObject C EInt)
    (h : ∀ X, (S.obj X).IsFirstQuadrant) : (assembleSpectralObject S).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    rw [Functor.isZero_iff]
    intro X
    let := h X
    exact (S.obj X).isZero₁_of_isFirstQuadrant i j hij hj n
  isZero₂ i j hij n hi := by
    rw [Functor.isZero_iff]
    intro X
    let := h X
    exact (S.obj X).isZero₂_of_isFirstQuadrant i j hij n hi

/-- The spectral object before extracting pages or a filtration, with its canonical
abutment and single-interval comparisons and the bottom augmentation on cocycles.

Source: Stacks Project, Tags 015N, 015J and 01F2.
(blueprint: lem-sc-topological-leray-spectral-object-augmentation)

Proof: Apply the Grothendieck construction to direct image and terminal sections.
Direct image preserves injectives; terminal sections is left exact. Mathlib
supplies the Grothendieck abelian and enough-injectives instances for abelian
sheaves on the small opens sites; no unbounded K-injective resolution is needed. The truncations
of the derived direct image give a first-quadrant spectral object, with interval
cohomology R^p Gamma_X(R^q f_* F). Use the Cartan--Eilenberg total augmentation
and its acyclic first filtration to compare the total cohomology with Gamma_Z(I).
These comparisons are natural: lifts of sheaf maps to resolutions and their
Cartan--Eilenberg resolutions are homotopic, and hence act identically on the
spectral object and on total cohomology. Identify the interval and abutment functors
with HX and HZ using hX and hZ. The bottom spectral-object map comes from the
resolution-degree-zero augmentation. On a resolution cocycle s its comparison
into f_*I is s followed by phi. The formula for a identifies global sections of
f_*I with those of I, so a followed by f_*z = s followed by phi identifies the
resulting cocycle with z. The canonical injective-resolution cohomology comparison
then gives I.extMk z. Comparison homotopies prove this for every I,J,phi, not just
the chosen resolutions. No pages, transitions, or filtration factorization are
asserted here; these belong to the separate generic spectral-object argument.
-/
theorem exists_topological_leray_spectral_object_augmentation
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
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
                eqToHom (Opens.map_top f))))) :
    ∃ Y : Abelian.SpectralObject
        (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) EInt,
      ∃ hY : Y.IsFirstQuadrant,
        ∃ h : ∀ n : ℕ, (Y.H n).obj
            (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ HZ n,
          ∃ e : ∀ p q : ℕ, (Y.H (p + q : ℕ)).obj
              (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) ≅
                (TopCat.Sheaf.pushforwardAb f).rightDerived q ⋙ HX p,
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
          ((Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero
              (HX p) ≫ (e p 0).inv ≫
            (@Abelian.SpectralObject.bottomEdge _ _ _ Y hY p) ≫ (h p).hom).app F
            ((eqToHom (congrArg (fun Q ↦ Q.obj
              ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
              (J.extMk s (p + 1) rfl hs))) =
            I.extMk z (p + 1) rfl hz) := by
  have hHX := funext hX
  subst HX
  have hHZ := funext hZ
  subst HZ
  let Fd := TopCat.Sheaf.pushforwardAb f
  let G := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  have : PreservesFiniteLimits Fd := by
    have adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Z)
    have : PreservesLimitsOfSize.{0, 0} Fd := adj.rightAdjoint_preservesLimits
    infer_instance
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have hFG : Fd.IsAcyclicComposablePair G := by
    intro M _ q hq
    have : Injective (Fd.obj M) := TopCat.Sheaf.injective_pushforwardAb_obj f M
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact G.isZero_rightDerived_obj_injective_succ k (Fd.obj M)
  obtain ⟨x, zc, computation⟩ :=
    exists_topological_terminal_resolution_ext_comparison f a ha
  let S := Fd.grothendieckSpectralObjectFunctor G
  let Y := assembleSpectralObject S
  have hY : Y.IsFirstQuadrant := assemble_firstQuadrant S (fun M ↦ inferInstance)
  let h (n : ℕ) := Fd.grothendieckSpectralObjectHBotTopIso G hFG n ≪≫ zc n
  let e (p q : ℕ) :=
    Fd.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
      (by push_cast; rfl) rfl rfl ≪≫ Functor.isoWhiskerLeft (Fd.rightDerived q) (x p)
  refine ⟨Y, hY, h, e, ?_⟩
  intro M I J φ hφ p s hs z hz hsz
  have cmp := computation M I J φ hφ p s hs z hz hsz
  have edge := grothendieckBottomEdgeMap_eq_resolution Fd G hFG M I J φ hφ p
  let := hY
  have bottom (n : ℤ) : (Y.bottomEdge n) = Fd.grothendieckBottomEdge G n := by
    have := Y.isIso_H_map_bot_zero_one n
    apply NatTrans.ext
    funext N
    simp only [Abelian.SpectralObject.bottomEdge, NatTrans.comp_app,
      Functor.grothendieckBottomEdge]
    rw [NatIso.isIso_inv_app]
    rfl
  have transport :
      Functor.whiskerRight Fd.toRightDerivedZero
          (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ≫
        (e p 0).inv ≫ Y.bottomEdge p ≫ (h p).hom =
      (Functor.isoWhiskerLeft Fd (x p)).inv ≫
        Fd.grothendieckBottomEdgeMap G hFG p ≫ (zc p).hom := by
    rw [bottom]
    dsimp [e, h, Functor.grothendieckBottomEdgeMap,
      Functor.grothendieckBottomEdgeSourceIso]
    apply NatTrans.ext
    funext N
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [← (x p).inv.naturality_assoc]
    simp only [Functor.rightDerivedZeroIsoSelf]
    congr 4
  rw [transport]
  simp only [eqToHom_refl, CategoryTheory.id_apply, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, CategoryTheory.comp_apply]
  rw [edge]
  exact cmp

end CategoryTheory
