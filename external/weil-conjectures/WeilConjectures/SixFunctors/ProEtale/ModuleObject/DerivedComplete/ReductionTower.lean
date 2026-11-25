/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafModuleZSMul
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic

/-!
# A derived complete `𝒪_E`-complex is the homotopy limit of its reductions modulo `ℓⁿ`

Let `K` be a derived complete complex of `𝒪_{E,X}`-module objects on `X_proét`
(`ProEtale.derivedCompleteIntegers`). Write `red_n` for the derived reduction modulo `ℓⁿ` and
`Res_n` for the restriction of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`. We show that `K` is the
homotopy limit of a tower `⋯ ⟶ Res_2 (red_2 K) ⟶ Res_1 (red_1 K)`, the legs being the units
`K ⟶ Res_n (red_n K)` of the adjunctions `red_n ⊣ Res_n`
(`ProEtale.exists_isHomotopyLimit_reductionTower`).

The transition maps are obtained (non-canonically) by completing the morphisms of natural
reduction triangles `K --ℓⁿ--> K ⟶ Res_n (red_n K) ⟶ K⟦1⟧` with first two components `ℓ` and `𝟙`.

## The triangulated argument

The general statement is `CategoryTheory.Pretriangulated.isHomotopyLimit_of_triangles`: let
`K --mⁿ⁺¹--> K --ηₙ--> Gₙ ⟶ K⟦1⟧` be a tower of distinguished triangles, with transition maps
`(m, 𝟙, tₙ)`, such that `𝟙 + m • x` is invertible for every endomorphism `x` of `∏ₙ K` and of
`(∏ₙ K)⟦1⟧`. Then the cone `(ηₙ)ₙ` is a homotopy limit cone. Taking the product of the triangles
and the endomorphism `𝟙 - t` of the product triangle `∏ K ⟶ ∏ K ⟶ ∏ G ⟶ (∏ K)⟦1⟧`, its first
component is invertible, and its second component has fibre `K` (the constant tower). The
octahedron axiom then yields an endomorphism `m₁` of `∏ G` with fibre `K`
(`CategoryTheory.Pretriangulated.exists_distTriang_of_endo_triangle`), and `𝟙 - t = m₁ ≫ θ`
for an automorphism `θ` of `∏ G` of the form `𝟙 + x ≫ y` where `𝟙 + y ≫ x` is invertible by the
assumption on `m`.

For derived complete `𝒪_E`-complexes, `𝟙 + ℓ • x` is invertible by derived Nakayama, since `ℓ`
acts by zero on the first derived reduction
(`ProEtale.isIso_id_add_zsmul_of_derivedCompleteIntegers`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory

/-- **Jacobson's lemma** in a preadditive category: if `𝟙 + g ≫ f` is an isomorphism, then so is
`𝟙 + f ≫ g`. -/
lemma isIso_id_add_comp_of_isIso {C : Type*} [Category* C] [Preadditive C] {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ X) [IsIso (𝟙 Y + g ≫ f)] : IsIso (𝟙 X + f ≫ g) := by
  have h₁ : g ≫ f ≫ inv (𝟙 Y + g ≫ f) = 𝟙 Y - inv (𝟙 Y + g ≫ f) := by
    have h := IsIso.hom_inv_id (𝟙 Y + g ≫ f)
    rw [Preadditive.add_comp, id_comp, assoc] at h
    exact eq_sub_of_add_eq' h
  have h₂ : inv (𝟙 Y + g ≫ f) ≫ g ≫ f = 𝟙 Y - inv (𝟙 Y + g ≫ f) := by
    have h := IsIso.inv_hom_id (𝟙 Y + g ≫ f)
    rw [Preadditive.comp_add, comp_id] at h
    exact eq_sub_of_add_eq' h
  refine ⟨𝟙 X - f ≫ inv (𝟙 Y + g ≫ f) ≫ g, ?_, ?_⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_sub, id_comp, comp_id, assoc,
      reassoc_of% h₁, Preadditive.sub_comp]
    abel
  · simp only [Preadditive.sub_comp, Preadditive.comp_add, id_comp, comp_id, assoc,
      reassoc_of% h₂, Preadditive.comp_sub]
    abel

/-- `mⁿ⁺¹ • 𝟙 = (m • 𝟙) ≫ (mⁿ • 𝟙)`, in the form of the commutativity of the first square of a
morphism `(m, 𝟙)` between triangles with first maps `mⁿ⁺¹ • 𝟙` and `mⁿ • 𝟙`. -/
lemma zsmul_pow_succ_id_comp_id {C : Type*} [Category* C] [Preadditive C] (m : ℤ) (K : C)
    (n : ℕ) : ((m ^ (n + 1)) • 𝟙 K) ≫ 𝟙 K = (m • 𝟙 K) ≫ ((m ^ n) • 𝟙 K) := by
  rw [comp_id, Preadditive.zsmul_comp, id_comp, smul_smul, ← pow_succ']

/-- The cone with point `K` over the tower `Functor.ofOpSequence t` of a sequence of morphisms
`t n : X (n + 1) ⟶ X n`, given by maps `η n : K ⟶ X n` with `η (n + 1) ≫ t n = η n`. -/
@[simps pt]
def Limits.Cone.ofOpSequence {C : Type*} [Category* C] {X : ℕ → C} (t : ∀ n, X (n + 1) ⟶ X n)
    (K : C) (η : ∀ n, K ⟶ X n) (h : ∀ n, η (n + 1) ≫ t n = η n) :
    Cone (Functor.ofOpSequence t) where
  pt := K
  π := NatTrans.ofOpSequence η fun n ↦ by
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.const_obj_map]
    exact (id_comp _).trans (h n).symm

@[simp]
lemma Limits.Cone.ofOpSequence_π_app {C : Type*} [Category* C] {X : ℕ → C}
    (t : ∀ n, X (n + 1) ⟶ X n) (K : C) (η : ∀ n, K ⟶ X n) (h : ∀ n, η (n + 1) ≫ t n = η n)
    (n : ℕ) : (Limits.Cone.ofOpSequence t K η h).π.app (Opposite.op n) = η n :=
  rfl

end CategoryTheory

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Let `φ` be an endomorphism of a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` such that
`φ.hom₁` is an isomorphism and `𝟙 + φ.hom₁⁻¹⟦1⟧ ≫ T.mor₁⟦1⟧ ≫ s` is an isomorphism for every
`s : T₂⟦1⟧ ⟶ T₁⟦1⟧`. If `X ⟶ T₂ ⟶ T₂ ⟶ X⟦1⟧` is a distinguished triangle with second map
`φ.hom₂`, then `X ⟶ T₂ ⟶ T₃` is the beginning of a distinguished triangle with second map
`φ.hom₃`: the fibre of `φ.hom₂` is also a fibre of `φ.hom₃`. -/
theorem exists_distTriang_of_endo_triangle (T : Triangle C) (hT : T ∈ distTriang C)
    (φ : T ⟶ T) [IsIso φ.hom₁]
    (hN : ∀ s : T.obj₂⟦(1 : ℤ)⟧ ⟶ T.obj₁⟦(1 : ℤ)⟧,
      IsIso (𝟙 _ + inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ T.mor₁⟦(1 : ℤ)⟧' ≫ s))
    {X : C} (x : X ⟶ T.obj₂) {δX : T.obj₂ ⟶ X⟦(1 : ℤ)⟧}
    (hX : Triangle.mk x φ.hom₂ δX ∈ distTriang C) :
    ∃ w : T.obj₃ ⟶ X⟦(1 : ℤ)⟧, Triangle.mk (x ≫ T.mor₂) φ.hom₃ w ∈ distTriang C := by
  have comm : (inv φ.hom₁ ≫ T.mor₁) ≫ φ.hom₂ = T.mor₁ := by
    rw [assoc, φ.comm₁, IsIso.inv_hom_id_assoc]
  have h₁₂ : Triangle.mk (inv φ.hom₁ ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ φ.hom₁⟦(1 : ℤ)⟧') ∈
      distTriang C :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (asIso φ.hom₁).symm (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by
        simp only [Triangle.mk_mor₃, Iso.symm_hom, asIso_inv, Iso.refl_hom, id_comp, assoc,
          ← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, comp_id]))
  have h₂₃ : Triangle.mk φ.hom₂ δX (-x⟦(1 : ℤ)⟧') ∈ distTriang C := rot_of_distTriang _ hX
  have h₁₃ : Triangle.mk T.mor₁ T.mor₂ T.mor₃ ∈ distTriang C := hT
  let O := Triangulated.someOctahedron comm h₁₂ h₂₃ h₁₃
  -- the fibre of `O.m₁` is `X`
  obtain ⟨w, hw⟩ : ∃ w : T.obj₃ ⟶ X⟦(1 : ℤ)⟧,
      Triangle.mk (x ≫ T.mor₂) O.m₁ w ∈ distTriang C := by
    let e : X ≅ X⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧ := (shiftEquiv C (1 : ℤ)).unitIso.app X
    refine ⟨(Triangle.mk O.m₁ O.m₃ ((-x⟦(1 : ℤ)⟧') ≫ T.mor₂⟦(1 : ℤ)⟧')).invRotate.mor₃ ≫
      e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ (inv_rot_of_distTriang _ O.mem) _
        (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_)⟩
    · simp only [e, Triangle.mk_mor₁, Iso.refl_hom, comp_id, Triangle.invRotate_mor₁,
        Triangle.mk_mor₃, Preadditive.neg_comp, Functor.map_neg, neg_neg, ← Functor.map_comp,
        Iso.app_hom]
      exact (NatIso.naturality_2 (shiftEquiv C (1 : ℤ)).unitIso _).symm
    · simp [← Functor.map_comp]
  -- `φ.hom₃ = O.m₁ ≫ θ` for an automorphism `θ`
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₃ T hT (φ.hom₃ - O.m₁) (by
    rw [Preadditive.comp_sub, φ.comm₂, O.comm₁, sub_self])
  have hδ : T.mor₃ ≫ h ≫ T.mor₃ = 0 := by
    rw [← assoc, ← hh, Preadditive.sub_comp, ← φ.comm₃, O.comm₂, sub_self]
  obtain ⟨s, hs⟩ := Triangle.yoneda_exact₃ T.rotate (rot_of_distTriang _ hT) (h ≫ T.mor₃) hδ
  have : IsIso (𝟙 _ + (inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ h) ≫ T.mor₃) := by
    have hs' : h ≫ T.mor₃ = T.mor₁⟦(1 : ℤ)⟧' ≫ (-s) := by
      rw [hs, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    rw [assoc, hs']
    exact hN (-s)
  have := isIso_id_add_comp_of_isIso T.mor₃ (inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ h)
  have hθ : φ.hom₃ = O.m₁ ≫ (𝟙 _ + T.mor₃ ≫ inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ h) := by
    rw [Preadditive.comp_add, comp_id, ← assoc O.m₁, O.comm₂, assoc, IsIso.hom_inv_id_assoc,
      ← hh, add_sub_cancel]
  refine ⟨inv (𝟙 _ + T.mor₃ ≫ inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ h) ≫ w,
    isomorphic_distinguished _ hw _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso (𝟙 _ + T.mor₃ ≫ inv (φ.hom₁⟦(1 : ℤ)⟧') ≫ h)).symm (by simp) ?_ (by simp))⟩
  simp only [Triangle.mk_mor₂, Iso.symm_hom, asIso_inv, Iso.refl_hom, id_comp]
  rw [hθ, assoc, IsIso.hom_inv_id, comp_id]

variable [HasLimitsOfShape (Discrete ℕ) C]

/-- Let `K --mⁿ⁺¹--> K --ηₙ--> Gₙ --δₙ--> K⟦1⟧` be distinguished triangles, where `ηₙ` are the legs
of a cone `c` with point `K` over a tower `G`, compatible with the transition maps of `G` and
the multiplication by `m` on `K`. If `𝟙 + m • x` is an isomorphism for every endomorphism `x` of
`∏ₙ K` and of `(∏ₙ K)⟦1⟧` (for instance if `K` is complete with respect to `m`, in a suitable
sense), then `c` is a homotopy limit cone: `K = R lim Gₙ`. -/
theorem isHomotopyLimit_of_triangles {G : ℕᵒᵖ ⥤ C} (c : Cone G) (m : ℤ)
    (δ : ∀ n : ℕ, G.obj (op n) ⟶ c.pt⟦(1 : ℤ)⟧)
    (hT : ∀ n : ℕ, Triangle.mk ((m ^ (n + 1)) • 𝟙 c.pt) (c.π.app (op n)) (δ n) ∈ distTriang C)
    (hδ : ∀ n : ℕ, δ (n + 1) ≫ (m • 𝟙 c.pt)⟦(1 : ℤ)⟧' = G.map (homOfLE n.le_succ).op ≫ δ n)
    (hN₀ : ∀ x : (∏ᶜ fun _ : ℕ ↦ c.pt) ⟶ ∏ᶜ fun _ : ℕ ↦ c.pt, IsIso (𝟙 _ + m • x))
    (hN₁ : ∀ x : (∏ᶜ fun _ : ℕ ↦ c.pt)⟦(1 : ℤ)⟧ ⟶ (∏ᶜ fun _ : ℕ ↦ c.pt)⟦(1 : ℤ)⟧,
      IsIso (𝟙 _ + m • x)) :
    IsHomotopyLimit c := by
  let T : ℕ → Triangle C := fun n ↦ Triangle.mk ((m ^ (n + 1)) • 𝟙 c.pt) (c.π.app (op n)) (δ n)
  have hPT : productTriangle T ∈ distTriang C := productTriangle_distinguished T hT
  let tr (n : ℕ) : T (n + 1) ⟶ T n :=
    Triangle.homMk _ _ (m • 𝟙 c.pt) (𝟙 c.pt) (G.map (homOfLE n.le_succ).op)
      (zsmul_pow_succ_id_comp_id m c.pt (n + 1))
      ((c.w _).trans (id_comp _).symm) (hδ n)
  let τ : productTriangle T ⟶ productTriangle T :=
    productTriangle.lift T fun n ↦ productTriangle.π T (n + 1) ≫ tr n
  let hPK : IsLimit (Fan.mk _ (Pi.π fun n ↦ (T n).obj₂)) := productIsProduct _
  let hPG : IsLimit (Fan.mk _ (Pi.π fun n ↦ (T n).obj₃)) := productIsProduct _
  have hτ₁ : τ.hom₁ = m • towerShift (F := (Functor.const ℕᵒᵖ).obj c.pt) hPK :=
    Fan.IsLimit.hom_ext hPK _ _ fun n ↦ by
      rw [Preadditive.zsmul_comp, towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₁, comp_hom₁, productTriangle.π_hom₁,
        Triangle.homMk_hom₁]
      exact (Pi.lift_comp_π _ _).trans (Preadditive.comp_zsmul _ _ _)
  have hτ₂ : τ.hom₂ = towerShift (F := (Functor.const ℕᵒᵖ).obj c.pt) hPK :=
    Fan.IsLimit.hom_ext hPK _ _ fun n ↦ by
      rw [towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₂, comp_hom₂, productTriangle.π_hom₂,
        Triangle.homMk_hom₂]
      exact Pi.lift_comp_π _ _
  have hτ₃ : τ.hom₃ = towerShift (F := G) hPG :=
    Fan.IsLimit.hom_ext hPG _ _ fun n ↦ by
      rw [towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₃, comp_hom₃, productTriangle.π_hom₃,
        Triangle.homMk_hom₃]
      exact Pi.lift_comp_π _ _
  let φ : productTriangle T ⟶ productTriangle T :=
    Triangle.homMk _ _ (𝟙 _ - τ.hom₁) (𝟙 _ - τ.hom₂) (𝟙 _ - τ.hom₃)
      (by rw [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, τ.comm₁])
      (by rw [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, τ.comm₂])
      (by
        rw [Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.comp_sub,
          Preadditive.sub_comp, comp_id, id_comp, τ.comm₃])
  have : IsIso φ.hom₁ := by
    have h : φ.hom₁ = 𝟙 _ + m • -towerShift (F := (Functor.const ℕᵒᵖ).obj c.pt) hPK := by
      rw [smul_neg, ← sub_eq_add_neg, ← hτ₁]
      rfl
    rw [h]
    exact hN₀ _
  have hmor₁ : (productTriangle T).mor₁ = m • Limits.Pi.map
      (f := fun n ↦ (T n).obj₁) (g := fun n ↦ (T n).obj₂) fun n ↦ (m ^ n) • 𝟙 c.pt :=
    Pi.hom_ext _ _ fun n ↦ by
      rw [productTriangle_mor₁, Limits.Pi.map_π, Preadditive.zsmul_comp, Limits.Pi.map_π,
        Preadditive.comp_zsmul, smul_smul, ← pow_succ']
      exact Preadditive.comp_zsmul _ _ _
  obtain ⟨δK, hK⟩ := (IsHomotopyLimit.of_isIso_π
    ({ pt := c.pt, π := 𝟙 _ } : Cone ((Functor.const ℕᵒᵖ).obj c.pt))).exists_distTriang hPK
  rw [← hτ₂] at hK
  obtain ⟨w, hw⟩ := exists_distTriang_of_endo_triangle _ hPT φ (fun s ↦ by
    rw [hmor₁, Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    exact hN₁ _) _ hK
  refine ⟨_, hPG, w, ?_⟩
  have h₁ : Fan.IsLimit.lift hPG (fun n ↦ c.π.app (op n)) =
      Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 c.pt) ≫ (productTriangle T).mor₂ :=
    Pi.hom_ext _ _ fun n ↦ by
      rw [assoc, productTriangle_mor₂, Limits.Pi.map_π, ← assoc]
      exact (Fan.IsLimit.fac hPG _ n).trans ((id_comp _).symm.trans
        (congrArg (· ≫ c.π.app (op n)) (Fan.IsLimit.fac hPK (fun _ ↦ 𝟙 c.pt) n).symm))
  rw [h₁, ← hτ₃]
  exact hw

end CategoryTheory.Pretriangulated

/-- In the derived category of an abelian category on which an integer `m` acts by zero,
`𝟙 + m • y` is an isomorphism for every endomorphism `y`: it induces the identity on homology. -/
lemma DerivedCategory.isIso_id_add_zsmul {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {m : ℤ} (hm : ∀ M : A, m • 𝟙 M = 0) {K : DerivedCategory A}
    (y : K ⟶ K) : IsIso (𝟙 K + m • y) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  rw [Functor.map_add, CategoryTheory.Functor.map_id, Functor.map_zsmul, ← comp_id
    ((DerivedCategory.homologyFunctor A i).map y), ← Preadditive.comp_zsmul, hm, comp_zero,
    add_zero]
  infer_instance

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] {X : Scheme.{u}}

-- rewriting `Functor.map_id` under `derivedReduction` unifies large instance terms for the
-- coercion of the `FiniteIntermediateField` `E` to a type
/-- **Derived Nakayama**: on a derived complete `𝒪_E`-complex `M`, the endomorphism
`𝟙 + ℓ • x` is an isomorphism for every endomorphism `x`, since `ℓ` acts by zero on the first
derived reduction. -/
theorem isIso_id_add_zsmul_of_derivedCompleteIntegers
    {M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hM : derivedCompleteIntegers ℓ E X M) (x : M ⟶ M) : IsIso (𝟙 M + (ℓ : ℤ) • x) := by
  refine isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map _ hM hM ?_
  have : (derivedReduction X ℓ E).Additive :=
    inferInstanceAs (((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor ⋙
      (residueFieldModuleSheaf X ℓ E).mapDerivedCategory).Additive)
  rw [Functor.map_add, CategoryTheory.Functor.map_id, Functor.map_zsmul]
  exact DerivedCategory.isIso_id_add_zsmul (Sheaf.zsmul_id_eq_zero_of_intCast_eq_zero
    (by rw [Int.cast_natCast, natCast_eq_zero_residueFieldCoeff])) _

/-- Derived complete complexes are closed under products. -/
theorem derivedCompleteIntegers_piObj {ι : Type*}
    (M : ι → DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) [HasProduct M]
    (hM : ∀ i, derivedCompleteIntegers ℓ E X (M i)) :
    derivedCompleteIntegers ℓ E X (∏ᶜ M) := by
  intro Z hZ f
  refine Pi.hom_ext _ _ fun i ↦ ?_
  rw [zero_comp]
  exact hM i hZ _

/-- The morphism `(ℓ, 𝟙)` from the natural reduction triangle modulo `ℓⁿ⁺²` of `K` to the one
modulo `ℓⁿ⁺¹` extends to a morphism of triangles. -/
lemma exists_reductionTowerTransition
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    ∃ t : (Mod.comap (integersModPowReduction X ℓ E (n + 1 + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars
          (integersModPowReduction X ℓ E (n + 1 + 1))).leftDerivedFunctor.obj K) ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K),
      (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction X ℓ E (n + 1 + 1))).unit.app K ≫ t =
        𝟙 K ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowReduction X ℓ E (n + 1))).unit.app K ∧
      (integersModPowReductionδ ℓ E (n + 1 + 1) X).app K ≫
          (shiftFunctor _ (1 : ℤ)).map ((ℓ : ℤ) • 𝟙 K) =
        t ≫ (integersModPowReductionδ ℓ E (n + 1) X).app K :=
  complete_distinguished_triangle_morphism _ _
    (integersModPowReduction_distinguished ℓ E (n + 1 + 1) K)
    (integersModPowReduction_distinguished ℓ E (n + 1) K) ((ℓ : ℤ) • 𝟙 K) (𝟙 K)
    (zsmul_pow_succ_id_comp_id _ K (n + 1))

variable (E) in
/-- A transition map `Res_{n+2} (red_{n+2} K) ⟶ Res_{n+1} (red_{n+1} K)` between the reductions
modulo `ℓⁿ⁺²` and `ℓⁿ⁺¹` of a complex `K` of `𝒪_{E,X}`-module objects, completing the morphism
`(ℓ, 𝟙)` between the natural reduction triangles to a morphism of triangles. -/
noncomputable def reductionTowerTransition
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (Mod.comap (integersModPowReduction X ℓ E (n + 1 + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars
          (integersModPowReduction X ℓ E (n + 1 + 1))).leftDerivedFunctor.obj K) ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K) :=
  (exists_reductionTowerTransition K n).choose

/-- The transition maps of the tower of reductions are compatible with the units. -/
@[reassoc (attr := simp)]
lemma unit_comp_reductionTowerTransition
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1 + 1))).unit.app K ≫
      reductionTowerTransition E K n =
    (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app K :=
  (exists_reductionTowerTransition K n).choose_spec.1.trans (id_comp _)

/-- The transition maps of the tower of reductions are compatible with the connecting morphisms
of the natural reduction triangles and with the multiplication by `ℓ`. -/
lemma reductionTowerTransition_comp_δ
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (integersModPowReductionδ ℓ E (n + 1 + 1) X).app K ≫
        (shiftFunctor _ (1 : ℤ)).map ((ℓ : ℤ) • 𝟙 K) =
      reductionTowerTransition E K n ≫ (integersModPowReductionδ ℓ E (n + 1) X).app K :=
  (exists_reductionTowerTransition K n).choose_spec.2

variable (E) in
/-- The tower `⋯ ⟶ Res_3 (red_3 K) ⟶ Res_2 (red_2 K) ⟶ Res_1 (red_1 K)` of reductions modulo
`ℓⁿ` of a complex `K` of `𝒪_{E,X}`-module objects; its `n`-th term is `Res_{n+1} (red_{n+1} K)`
(`ProEtale.reductionTower_obj`). -/
noncomputable def reductionTower
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :=
  Functor.ofOpSequence (X := fun n ↦
    (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K))
    (reductionTowerTransition E K)

@[simp]
lemma reductionTower_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (reductionTower E K).obj (op n) =
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj
          K) :=
  rfl

@[simp]
lemma reductionTower_map_succ
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (reductionTower E K).map (homOfLE (Nat.le_add_right n 1)).op =
      reductionTowerTransition E K n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

variable (E) in
/-- The cone over the tower of reductions of `K` with point `K`, whose legs are the units
`K ⟶ Res_{n+1} (red_{n+1} K)` of the adjunctions `red_{n+1} ⊣ Res_{n+1}`. -/
noncomputable def reductionTowerCone
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    Cone (reductionTower E K) :=
  Limits.Cone.ofOpSequence (X := fun n ↦
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K))
    (reductionTowerTransition E K) K (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E (n + 1))).unit.app K) (unit_comp_reductionTowerTransition K)

@[simp]
lemma reductionTowerCone_pt
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    (reductionTowerCone E K).pt = K :=
  rfl

@[simp]
lemma reductionTowerCone_π_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℕ) :
    (reductionTowerCone E K).π.app (op n) = (Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X ℓ E (n + 1))).unit.app K :=
  rfl

/-- **A derived complete `𝒪_E`-complex is the homotopy limit of its reductions modulo `ℓⁿ`**:
the cone `K ⟶ Res_{n+1} (red_{n+1} K)` of units of `red_{n+1} ⊣ Res_{n+1}` is a homotopy limit
cone, `K = R lim_n Res_n (red_n K)`. -/
theorem isHomotopyLimit_reductionTowerCone
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) : IsHomotopyLimit (reductionTowerCone E K) := by
  have hP : derivedCompleteIntegers ℓ E X (∏ᶜ fun _ : ℕ ↦ K) :=
    derivedCompleteIntegers_piObj _ fun _ ↦ hK
  refine isHomotopyLimit_of_triangles _ (ℓ : ℤ)
    (fun n ↦ (integersModPowReductionδ ℓ E (n + 1) X).app K)
    (fun n ↦ integersModPowReduction_distinguished ℓ E (n + 1) K) (fun n ↦ ?_)
    (isIso_id_add_zsmul_of_derivedCompleteIntegers hP)
    (isIso_id_add_zsmul_of_derivedCompleteIntegers (derivedCompleteIntegers_shift hP 1))
  rw [reductionTower_map_succ]
  exact reductionTowerTransition_comp_δ K n

/-- **A derived complete `𝒪_E`-complex is the homotopy limit of its reductions modulo `ℓⁿ`**:
there is a homotopy limit cone with point `K` over the tower `reductionTower E K`, whose `n`-th
term is `Res_{n+1} (red_{n+1} K)` (`ProEtale.reductionTower_obj`), the legs being the units of
the adjunctions `red_{n+1} ⊣ Res_{n+1}`. -/
theorem exists_isHomotopyLimit_reductionTower
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    ∃ π : (Functor.const ℕᵒᵖ).obj K ⟶ reductionTower E K, IsHomotopyLimit (Cone.mk K π) ∧
      ∀ n : ℕ, π.app (op n) = (Mod.derivedExtendMapDerivedCategoryAdjunction
        (integersModPowReduction X ℓ E (n + 1))).unit.app K :=
  ⟨(reductionTowerCone E K).π, isHomotopyLimit_reductionTowerCone hK, fun _ ↦ rfl⟩

end AlgebraicGeometry.ProEtale
