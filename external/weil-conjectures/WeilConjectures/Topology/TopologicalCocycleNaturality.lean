/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import all WeilConjectures.Topology.TopologicalResolutionCocycleLift

/-! # Naturality of topological cocycle comparisons -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace CategoryTheory
private theorem terminal_comparison_bijective
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
    (M : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    Function.Bijective (fun z : (presheafToSheaf (Opens.grothendieckTopology Z)
      AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ M ↦
        a ≫ (TopCat.Sheaf.pushforwardAb f).map z) := by
  let P := TopCat.Sheaf.pushforwardAb f
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
  exact hbij M

-- The target complex need not be a resolution or exact.
private theorem null_comparison_cycles
    {C : Type*} [Category C] [Abelian C] {F A : C} (J : InjectiveResolution F)
    (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)]
    (δ : J.cocomplex ⟶ K) (hδ : J.ι.f 0 ≫ δ.f 0 = 0) :
    (∀ s : A ⟶ J.cocomplex.X 0, s ≫ J.cocomplex.d 0 1 = 0 → s ≫ δ.f 0 = 0) ∧
    (∀ n (s : A ⟶ J.cocomplex.X (n + 1)),
      s ≫ J.cocomplex.d (n + 1) (n + 2) = 0 →
      ∃ b : A ⟶ K.X n, b ≫ K.d n (n + 1) = s ≫ δ.f (n + 1)) := by
  let t₀ := J.exact₀.descToInjective (δ.f 0) hδ
  have ht₀ : J.cocomplex.d 0 1 ≫ t₀ = δ.f 0 :=
    J.exact₀.comp_descToInjective _ _
  have steps : ∀ n, ∃ (t : J.cocomplex.X (n + 1) ⟶ K.X n)
      (t' : J.cocomplex.X (n + 2) ⟶ K.X (n + 1)),
      δ.f (n + 1) = t ≫ K.d n (n + 1) + J.cocomplex.d (n + 1) (n + 2) ≫ t' := by
    intro n
    induction n with
    | zero =>
      have h : J.cocomplex.d 0 1 ≫ (δ.f 1 - t₀ ≫ K.d 0 1) = 0 := by
        rw [Preadditive.comp_sub, ← Category.assoc, ht₀, δ.comm, sub_self]
      refine ⟨t₀, (J.exact_succ 0).descToInjective _ h, ?_⟩
      rw [(J.exact_succ 0).comp_descToInjective]
      exact (add_sub_cancel _ _).symm
    | succ n ih =>
      obtain ⟨t, t', ht⟩ := ih
      have h : J.cocomplex.d (n + 1) (n + 2) ≫
          (δ.f (n + 2) - t' ≫ K.d (n + 1) (n + 2)) = 0 := by
        rw [Preadditive.comp_sub, ← δ.comm, ht, Preadditive.add_comp]
        simp only [Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_add]
        simp
      refine ⟨t', (J.exact_succ (n + 1)).descToInjective _ h, ?_⟩
      rw [(J.exact_succ (n + 1)).comp_descToInjective]
      exact (add_sub_cancel _ _).symm
  constructor
  · intro s hs
    rw [← ht₀, ← Category.assoc, hs, zero_comp]
  · intro n s hs
    obtain ⟨t, t', ht⟩ := steps n
    refine ⟨s ≫ t, ?_⟩
    rw [ht, Preadditive.comp_add]
    simp only [Category.assoc, reassoc_of% hs, zero_comp, add_zero]

private theorem comparison_extMk_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasExt D]
    (P : D ⥤ C) [P.Additive] {A : C} {B Y : D} (a : A ⟶ P.obj B)
    (hbij : ∀ T : D, Function.Bijective (fun z : B ⟶ T ↦ a ≫ P.map z))
    {F : C} (J : InjectiveResolution F) (I : InjectiveResolution Y)
    [∀ n, Injective (P.obj (I.cocomplex.X n))]
    (φ ψ : J.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφψ : J.ι.f 0 ≫ φ.f 0 = J.ι.f 0 ≫ ψ.f 0)
    (p : ℕ) (s : A ⟶ J.cocomplex.X p) (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
    (z w : B ⟶ I.cocomplex.X p)
    (hz : z ≫ I.cocomplex.d p (p + 1) = 0)
    (hw : w ≫ I.cocomplex.d p (p + 1) = 0)
    (hzi : a ≫ P.map z = s ≫ φ.f p) (hwi : a ≫ P.map w = s ≫ ψ.f p) :
    I.extMk z (p + 1) rfl hz = I.extMk w (p + 1) rfl hw := by
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hδ : J.ι.f 0 ≫ (φ - ψ).f 0 = 0 := by
    change J.ι.f 0 ≫ (φ.f 0 - ψ.f 0) = 0
    rw [Preadditive.comp_sub, hφψ, sub_self]
  have hi : a ≫ P.map (z - w) = s ≫ (φ - ψ).f p := by
    change a ≫ P.map (z - w) = s ≫ (φ.f p - ψ.f p)
    rw [P.map_sub, Preadditive.comp_sub, Preadditive.comp_sub, hzi, hwi]
  have (n : ℕ) : Injective (K.X n) := inferInstanceAs (Injective (P.obj (I.cocomplex.X n)))
  obtain ⟨hzero, hsucc⟩ := null_comparison_cycles J K (φ - ψ) hδ
  cases p with
  | zero =>
    have hzw : z - w = 0 := (hbij _).injective (by
      rw [hi, hzero s hs]
      simp)
    have heq : z = w := sub_eq_zero.mp hzw
    subst w
    rfl
  | succ n =>
    obtain ⟨b, hb⟩ := hsucc n s hs
    obtain ⟨c, hc⟩ := (hbij (I.cocomplex.X n)).surjective b
    have hboundary : c ≫ I.cocomplex.d n (n + 1) = z - w := by
      apply (hbij _).injective
      change a ≫ P.map (c ≫ I.cocomplex.d n (n + 1)) = a ≫ P.map (z - w)
      dsimp only at hc
      rw [P.map_comp, ← Category.assoc, hc, hi]
      exact hb
    apply sub_eq_zero.mp
    rw [I.sub_extMk z w (n + 1 + 1) rfl hz hw]
    exact (I.extMk_eq_zero_iff _ _ rfl _ n rfl).2 ⟨c, hboundary⟩

-- The two proof witnesses in the cocycle-formula hypothesis have their original names.
set_option linter.unusedVariables false in
/-- The objectwise comparison maps are natural in the coefficient sheaf.
Source: Stacks Project, Cohomology, Section 20.2 (Tag 01DZ); Derived Categories,
Section 13.18, Lemmas 13.18.6 and 13.18.7, applied to the coefficient-map square.
(blueprint: lem-sc-topological-cocycle-naturality)

Proof: Represent an arbitrary class by a cycle s in a resolution J of f_*F.
Lift g:F -> G between resolutions I and I', and f_*g between resolutions J and J'.
The resolution-cocycle lifting theorem supplies comparisons phi:J -> f_*I and
phi':J' -> f_*I' and matching cycles z and z' (the latter for s followed by the
lift of f_*g). The composites J -> f_*I' have the same augmentation. Their difference
is zero on the augmentation, and the target terms are injective. Exactness of J
therefore factors its degree-zero component through d^0. Inductively, subtract the
previous homotopy term composed with the target differential and factor the remainder
through the next source differential. Precomposing with s kills the source-differential
term: in degree zero the result is zero, and in a positive degree it is a boundary.

The sheafification, free-forgetful and Yoneda adjunctions represent terminal sections.
The generator equation ha and naturality identify z mapping to a followed by f_*z
with restriction along the equality f^{-1}(X)=Z, hence this map is bijective in every
coefficient sheaf. Transfer the boundary just found through that bijection. Thus z'
and z followed by the resolution lift of g have the same Ext class, using
InjectiveResolution.sub_extMk and extMk_eq_zero_iff (and direct equality in degree zero).
Apply hτ to both matching cycles. InjectiveResolution.extMk_comp_mk₀ computes both
coefficient maps on their classes, so the two paths agree on s. Surjectivity of extMk
and extensionality of additive homomorphisms finish the naturality square. The argument
uses no exactness of f_*I' and covers degree zero and zero coefficient maps.
-/
theorem topological_cocycle_naturality
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
    (τ : ∀ (p : ℕ) (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}),
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj
        ((TopCat.Sheaf.pushforwardAb f).obj F) ⟶
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj F)
    (hτ : ∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (hφ : J.ι.f 0 ≫ φ.f 0 =
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
        (hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        τ p F (J.extMk s (p + 1) rfl hs) = I.extMk z (p + 1) rfl hz) :
    ∀ (p : ℕ) {F G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
      (g : F ⟶ G),
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
        ((TopCat.Sheaf.pushforwardAb f).map g) ≫ τ p G =
        τ p F ≫ (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map g := by
  intro p F G g
  let P := TopCat.Sheaf.pushforwardAb f
  let I := injectiveResolution F
  let I' := injectiveResolution G
  let J := injectiveResolution (P.obj F)
  let J' := injectiveResolution (P.obj G)
  let γ : I.Hom I' g :=
    ⟨InjectiveResolution.desc g I' I, by
      simp [InjectiveResolution.desc_commutes_zero]⟩
  let β : J.Hom J' (P.map g) :=
    ⟨InjectiveResolution.desc (P.map g) J' J, by
      simp [InjectiveResolution.desc_commutes_zero]⟩
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨s, hs, rfl⟩ := J.extMk_surjective x (p + 1) rfl
  obtain ⟨φ, hφ, z, hz, hsz⟩ :=
    exists_topological_resolution_cocycle_lift f a ha F I J p s hs
  have hs' : (s ≫ β.hom.f p) ≫ J'.cocomplex.d p (p + 1) = 0 := by
    simp [reassoc_of% hs]
  obtain ⟨φ', hφ', z', hz', hsz'⟩ :=
    exists_topological_resolution_cocycle_lift f a ha G I' J' p (s ≫ β.hom.f p) hs'
  have hzγ : (z ≫ γ.hom.f p) ≫ I'.cocomplex.d p (p + 1) = 0 := by
    simp [reassoc_of% hz]
  have hinj (n : ℕ) : Injective (P.obj (I'.cocomplex.X n)) :=
    TopCat.Sheaf.injective_pushforwardAb_obj f _
  have hcomm : J.ι.f 0 ≫
      (φ ≫ (P.mapHomologicalComplex (ComplexShape.up ℕ)).map γ.hom).f 0 =
      J.ι.f 0 ≫ (β.hom ≫ φ').f 0 := by
    change J.ι.f 0 ≫ φ.f 0 ≫ P.map (γ.hom.f 0) =
      J.ι.f 0 ≫ β.hom.f 0 ≫ φ'.f 0
    rw [← Category.assoc, hφ, ← P.map_comp, γ.ι_f_zero_comp_hom_f_zero]
    rw [← Category.assoc, β.ι_f_zero_comp_hom_f_zero]
    simp only [CochainComplex.single₀_map_f_zero]
    rw [Category.assoc, hφ', P.map_comp]
  have hzcomp : a ≫ P.map (z ≫ γ.hom.f p) =
      s ≫ (φ ≫ (P.mapHomologicalComplex (ComplexShape.up ℕ)).map γ.hom).f p := by
    change a ≫ P.map (z ≫ γ.hom.f p) = s ≫ φ.f p ≫ P.map (γ.hom.f p)
    rw [P.map_comp, ← Category.assoc, hsz, Category.assoc]
  have hz'comp : a ≫ P.map z' = s ≫ (β.hom ≫ φ').f p := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using hsz'
  have heq := comparison_extMk_eq P a (terminal_comparison_bijective f a ha)
    J I' (φ ≫ (P.mapHomologicalComplex (ComplexShape.up ℕ)).map γ.hom)
    (β.hom ≫ φ') hcomm p s hs (z ≫ γ.hom.f p) z' hzγ hz' hzcomp hz'comp
  change τ p G ((J.extMk s (p + 1) rfl hs).comp
      (Abelian.Ext.mk₀ (P.map g)) (add_zero p)) =
    (τ p F (J.extMk s (p + 1) rfl hs)).comp (Abelian.Ext.mk₀ g) (add_zero p)
  rw [InjectiveResolution.extMk_comp_mk₀ s (p + 1) rfl hs β,
    hτ G I' J' φ' hφ' p (s ≫ β.hom.f p) hs' z' hz' hsz',
    hτ F I J φ hφ p s hs z hz hsz,
    InjectiveResolution.extMk_comp_mk₀ z (p + 1) rfl hz γ]
  exact heq.symm

end CategoryTheory
