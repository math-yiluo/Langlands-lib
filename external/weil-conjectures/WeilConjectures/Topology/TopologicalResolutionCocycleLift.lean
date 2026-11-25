/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution


/-! # Comparing topological resolution cocycles -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

private theorem exists_comparison
    {C : Type*} [Category C] [Abelian C] {F : C} (J : InjectiveResolution F)
    (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)]
    (b : F ⟶ K.X 0) (hb : b ≫ K.d 0 1 = 0) :
    ∃ φ : J.cocomplex ⟶ K, J.ι.f 0 ≫ φ.f 0 = b := by
  let g₀ := Injective.factorThru b (J.ι.f 0)
  have hg₀ : J.ι.f 0 ≫ g₀ = b := Injective.comp_factorThru _ _
  have h₀ : J.ι.f 0 ≫ (g₀ ≫ K.d 0 1) = 0 := by rw [← Category.assoc, hg₀, hb]
  let g₁ := J.exact₀.descToInjective (g₀ ≫ K.d 0 1) h₀
  have hg₁ : g₀ ≫ K.d 0 1 = J.cocomplex.d 0 1 ≫ g₁ :=
    (J.exact₀.comp_descToInjective _ _).symm
  let φ := CochainComplex.mkHom J.cocomplex K g₀ g₁ hg₁
    (fun n ⟨g, g', w⟩ ↦
      ⟨(J.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2))
          (by rw [← Category.assoc, ← w, Category.assoc]; simp),
        ((J.exact_succ n).comp_descToInjective _ _).symm⟩)
  exact ⟨φ, hg₀⟩

private noncomputable def sectionEquiv
    {C : Type*} [Category.{u} C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] (U : C) (M : Sheaf T AddCommGrpCat.{u}) :
    ((presheafToSheaf T AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ M) ≃ M.obj.obj (op U) :=
  ((sheafificationAdjunction T AddCommGrpCat.{u}).homEquiv _ M).trans
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj U) M.obj).trans
      yonedaEquiv)

private lemma sectionEquiv_apply
    {C : Type*} [Category.{u} C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}] (U : C) (M : Sheaf T AddCommGrpCat.{u})
    (z : (presheafToSheaf T AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ M) :
    sectionEquiv T U M z = z.hom.app (op U)
      ((toSheafify T (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
        (FreeAbelianGroup.of (𝟙 U))) := by
  rfl

/-- A cocycle on a resolution of f_*F can be compared with a resolution of F
and lifted uniquely as a terminal-section cocycle on the latter.

Source: Stacks Project, Tag 01F2 and the injective-resolution comparison construction,
with terminal sections represented by the free abelian terminal sheaf (Tag 01DZ).
(blueprint: lem-sc-topological-resolution-cocycle-lift)

Proof: Every term of f_*I is injective, since inverse image is exact and left adjoint
to direct image. Extend f_*(I.ι) across the monomorphism J.ι in degree zero using
injectivity. Inductively factor the preceding differential through the cokernel of
the preceding source differential, using exactness of the augmented resolution J;
extend across its monomorphism into the next term of J using injectivity of the
corresponding term of f_*I. This constructs phi and its augmentation equation.
The terminal-section representation gives a bijection between maps KZ -> I^p
and maps KX -> f_*I^p, realized by z mapping to a composed with f_*z: ha specifies
this bijection on the sheafification generators, which determine the morphism.
Apply its inverse to s composed with phi^p to obtain z and the stated equality.
The chain-map identity and hs make s composed with phi^p a cocycle. Apply the
same terminal-section bijection in degree p+1 to deduce hz. This argument uses
no exactness of f_* and works in degree zero and for the zero sheaf.
-/
theorem exists_topological_resolution_cocycle_lift
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
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
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
    (p : ℕ)
    (s : (presheafToSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
            J.cocomplex.X p)
    (hs : s ≫ J.cocomplex.d p (p + 1) = 0) :
    ∃ (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ φ.f 0 = (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0) ∧
      ∃ (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
            I.cocomplex.X p),
        z ≫ I.cocomplex.d p (p + 1) = 0 ∧
        a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p := by
  let P := TopCat.Sheaf.pushforwardAb f
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have (n : ℕ) : Injective (K.X n) :=
    TopCat.Sheaf.injective_pushforwardAb_obj f (I.cocomplex.X n)
  obtain ⟨φ, hφ⟩ := exists_comparison J K (P.map (I.ι.f 0)) (by
    change P.map (I.ι.f 0) ≫ P.map (I.cocomplex.d 0 1) = 0
    rw [← P.map_comp, I.ι_f_zero_comp_complex_d, P.map_zero])
  refine ⟨φ, hφ, ?_⟩
  have hbij (M : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
      Function.Bijective (fun z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ M ↦ a ≫ P.map z) := by
    let eZ := sectionEquiv (Opens.grothendieckTopology Z) (⊤ : Opens Z) M
    let eX := sectionEquiv (Opens.grothendieckTopology X) (⊤ : Opens X) (P.obj M)
    let e := eqToHom (Opens.map_top f)
    let r := (Iso.addCommGroupIsoToAddEquiv (M.obj.mapIso (asIso e.op))).toEquiv
    have he (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ M) :
        eX (a ≫ P.map z) = r (eZ z) := by
      rw [sectionEquiv_apply]
      change z.hom.app (op ((Opens.map f).obj ⊤))
        (a.hom.app (op ⊤) _) = _
      rw [ha ⊤ (𝟙 _)]
      let t := toSheafify (Opens.grothendieckTopology Z)
        (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ≫ z.hom
      have ht := ConcreteCategory.congr_hom (t.naturality e.op)
        (FreeAbelianGroup.of (𝟙 (⊤ : Opens Z)))
      simp [t, e, r, eZ, sectionEquiv_apply] at ht ⊢
    constructor
    · intro z z' h
      apply eZ.injective
      exact r.injective ((he z).symm.trans ((congrArg eX h).trans (he z')))
    · intro t
      obtain ⟨z, hz⟩ := eZ.surjective (r.symm (eX t))
      refine ⟨z, eX.injective ?_⟩
      rw [he z, hz, r.apply_symm_apply]
  obtain ⟨z, hz⟩ := (hbij (I.cocomplex.X p)).surjective (s ≫ φ.f p)
  dsimp only at hz
  refine ⟨z, ?_, hz⟩
  apply (hbij (I.cocomplex.X (p + 1))).injective
  change a ≫ P.map (z ≫ I.cocomplex.d p (p + 1)) = a ≫ P.map 0
  rw [P.map_comp, ← Category.assoc, hz, Category.assoc]
  change s ≫ φ.f p ≫ K.d p (p + 1) = a ≫ P.map 0
  rw [φ.comm p (p + 1), ← Category.assoc, hs]
  simp

end CategoryTheory
