/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.FromJoel.Algebra.Homology.Double
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Biproduct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-!
# Derived tensor products and duals of cokernels of endomorphisms of the unit

Let `C` be a Grothendieck abelian closed symmetric monoidal category with functorial flat
resolutions, so that `D(C)` is monoidal. For a monomorphism `g : X ⟶ Y`, the cokernel of `g`
placed in degree `i₀ + 1` is represented by the two-term complex `X --g--> Y` in degrees `i₀`,
`i₀ + 1` (`DerivedCategory.nonempty_Q_obj_double_iso_singleFunctor_obj_cokernel`). This gives:

* for flat `X`, `Y`, the derived tensor product of `coker(g)[0]` with `N[0]` is the two-term
  complex `X ⊗ N --g ▷ N--> Y ⊗ N` (`DerivedCategory.QObjDoubleTensorSingleFunctorObjIso`);
  hence, for monomorphisms `g a : 𝟙 ⟶ 𝟙` with `g a` acting by zero on `coker (g b)` for `b ≤ a`,
  the derived tensor product of two objects `⊕ⱼ coker (g (e j)) ⊕ 𝟙ʳ` has cohomology objects
  built from the unit and the `coker (g a)`, concentrated in degrees `-1` and `0`
  (`DerivedCategory.torConcentrated_biprod_cokernel_unit`);
* for `X`, `Y` with right duals, `coker(g)[q]` has the bounded left dual `Yᘁ --±gᘁ--> Xᘁ` in
  degrees `-q`, `-q + 1` (`DerivedCategory.exists_exactPairing_singleFunctor_cokernel`); hence
  `(⊕ⱼ coker (g (e j)) ⊕ 𝟙ʳ)[q]` has a bounded left dual with cohomology objects cokernels of
  endomorphisms of the unit, the unit, or zero
  (`DerivedCategory.hasBoundedDual_singleFunctor_biprod_cokernel_unit`).

These are the inputs for the constant `𝒪_E`-modules `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantDerived`). This file
does not import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory HomologicalComplex ZeroObject

namespace CochainComplex

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

/-- If `K^{i-1}` vanishes, the cohomology `Hⁱ(K)` is the kernel of the differential
`K^i ⟶ K^{i+1}`. -/
noncomputable def homologyIsoKernel (i j : ℤ) (hij : i + 1 = j) (h : IsZero (K.X (i - 1))) :
    K.homology i ≅ kernel (K.d i j) :=
  (K.isoHomologyπ (i - 1) i (by simp) (h.eq_of_src _ _)).symm ≪≫
    IsLimit.conePointUniqueUpToIso (K.cyclesIsKernel i j (by simp; omega)) (limit.isLimit _)

/-- If `K^{j+1}` vanishes, the cohomology `Hʲ(K)` is the cokernel of the differential
`K^{j-1} ⟶ K^j`. -/
noncomputable def homologyIsoCokernel (i j : ℤ) (hij : i + 1 = j) (h : IsZero (K.X (j + 1))) :
    K.homology j ≅ cokernel (K.d i j) :=
  K.isoHomologyι j (j + 1) (by simp) (h.eq_of_tgt _ _) ≪≫
    IsColimit.coconePointUniqueUpToIso (K.opcyclesIsCokernel i j (by simp; omega))
      (colimit.isColimit _)

end Homology

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (g : X ⟶ Y) {i₀ i₁ : ℤ}
  (h : (ComplexShape.up ℤ).Rel i₀ i₁)

/-- The two-term complex `X --g--> Y` in degrees `i₀`, `i₀ + 1` vanishes below `i₀`. -/
lemma isStrictlyGE_double : IsStrictlyGE (double g h) i₀ := by
  have : i₀ + 1 = i₁ := h
  rw [isStrictlyGE_iff]
  intro i hi
  exact isZero_double_X _ _ _ (by omega) (by omega)

/-- The two-term complex `X --g--> Y` in degrees `i₀`, `i₀ + 1` vanishes above `i₀ + 1`. -/
lemma isStrictlyLE_double : IsStrictlyLE (double g h) i₁ := by
  have : i₀ + 1 = i₁ := h
  rw [isStrictlyLE_iff]
  intro i hi
  exact isZero_double_X _ _ _ (by omega) (by omega)

/-- The cohomology of the two-term complex `X --g--> Y` vanishes outside its two degrees. -/
lemma isZero_double_homology {n : ℤ} (h₀ : n ≠ i₀) (h₁ : n ≠ i₁) :
    IsZero ((double g h).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_double_X g h _ h₀ h₁)

/-- The cohomology in degree `i₀` of the two-term complex `X --g--> Y` is the kernel of `g`. -/
noncomputable def doubleHomologyIso₀ : (double g h).homology i₀ ≅ kernel g :=
  have h' : i₀ + 1 = i₁ := h
  homologyIsoKernel _ i₀ i₁ h' (isZero_double_X g h _ (by omega) (by omega)) ≪≫
    kernel.mapIso _ _ (doubleXIso₀ g h) (doubleXIso₁ g h (by omega))
      (by simp [double_d _ h (show i₀ ≠ i₁ by omega)])

/-- The cohomology in degree `i₀ + 1` of the two-term complex `X --g--> Y` is the cokernel of
`g`. -/
noncomputable def doubleHomologyIso₁ : (double g h).homology i₁ ≅ cokernel g :=
  have h' : i₀ + 1 = i₁ := h
  homologyIsoCokernel _ i₀ i₁ h' (isZero_double_X g h _ (by omega) (by omega)) ≪≫
    cokernel.mapIso _ _ (doubleXIso₀ g h) (doubleXIso₁ g h (by omega))
      (by simp [double_d _ h (show i₀ ≠ i₁ by omega)])

end CochainComplex

namespace CategoryTheory

namespace Limits

variable {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]
  [HasBinaryBiproducts D]

/-- A property of objects which holds for zero objects, is invariant under isomorphisms and
stable under binary biproducts holds for all finite biproducts indexed by `Fin k`. -/
lemma prop_biproduct_of_forall (P : D → Prop) (hiso : ∀ {X Y : D}, (X ≅ Y) → P X → P Y)
    (h0 : ∀ X : D, IsZero X → P X) (h2 : ∀ X Y : D, P X → P Y → P (X ⊞ Y)) :
    ∀ {k : ℕ} (f : Fin k → D), (∀ j, P (f j)) → P (⨁ f)
  | 0, _, _ => h0 _ (isZero_biproduct_fin_zero _)
  | _ + 1, f, hf => hiso (biproductFinSuccIso f).symm
      (h2 _ _ (hf 0) (prop_biproduct_of_forall P hiso h0 h2 _ fun j ↦ hf j.succ))

end Limits

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The mate of an isomorphism is an isomorphism between the right duals. -/
@[simps]
def rightAdjointMateIso {A B : C} [HasRightDual A] [HasRightDual B] (e : A ≅ B) : Bᘁ ≅ Aᘁ where
  hom := e.homᘁ
  inv := e.invᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate, e.inv_hom_id, rightAdjointMate_id]
  inv_hom_id := by rw [← comp_rightAdjointMate, e.hom_inv_id, rightAdjointMate_id]

/-- For the canonical self-duality of the unit, the mate of an endomorphism of the unit is the
endomorphism itself. -/
lemma rightAdjointMate_tensorUnit (g : 𝟙_ C ⟶ 𝟙_ C) : gᘁ = g := by
  have hη : η_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).inv := rfl
  have hε : ε_ (𝟙_ C) (𝟙_ C)ᘁ = (ρ_ _).hom := rfl
  rw [rightAdjointMate, hη, hε]
  monoidal

end CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {X Y : C} (g : X ⟶ Y) {i₀ i₁ : ℤ} (h : (ComplexShape.up ℤ).Rel i₀ i₁)

omit [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
/-- A two-term complex `X --g--> Y` with `g` a monomorphism is quasi-isomorphic to the cokernel
of `g` placed in the degree of `Y`. -/
lemma nonempty_Q_obj_double_iso_singleFunctor_obj_cokernel [Mono g] :
    Nonempty (Q.obj (double g h) ≅ (singleFunctor C i₁).obj (cokernel g)) := by
  have h' : i₀ + 1 = i₁ := h
  have := CochainComplex.isStrictlyLE_double g h
  have : (Q.obj (double g h)).IsGE i₁ := by
    rw [isGE_Q_obj_iff, CochainComplex.isGE_iff]
    intro i hi
    rw [exactAt_iff_isZero_homology]
    by_cases hi₀ : i = i₀
    · subst hi₀
      exact (CochainComplex.doubleHomologyIso₀ g h).isZero_iff.2 (isZero_kernel_of_mono g)
    · exact CochainComplex.isZero_double_homology g h hi₀ (by omega)
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj (double g h)) i₁
  exact ⟨e ≪≫ (singleFunctor C i₁).mapIso
    (((singleFunctorCompHomologyFunctorIso C i₁).app M).symm ≪≫
    (homologyFunctor C i₁).mapIso e.symm ≪≫ (homologyFunctorFactors C i₁).app _ ≪≫
    CochainComplex.doubleHomologyIso₁ g h)⟩

omit [IsGrothendieckAbelian.{v} C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
/-- The terms of the two-term complex `X --g--> Y` are flat if `X` and `Y` are. -/
lemma flat_double_X (hX : ObjectProperty.flat X) (hY : ObjectProperty.flat Y) (n : ℤ) :
    ObjectProperty.flat ((double g h).X n) := by
  have h' : i₀ + 1 = i₁ := h
  by_cases h₀ : n = i₀
  · subst h₀
    exact ObjectProperty.prop_of_iso _ (doubleXIso₀ g h).symm hX
  by_cases h₁ : n = i₁
  · subst h₁
    exact ObjectProperty.prop_of_iso _ (doubleXIso₁ g h (by omega)).symm hY
  exact ObjectProperty.flat_of_isZero (isZero_double_X g h n h₀ h₁)

/-- For flat `X` and `Y`, the derived tensor product of the two-term complex `X --g--> Y` with
`N[0]` is the two-term complex `X ⊗ N --g ▷ N--> Y ⊗ N`. -/
noncomputable def QObjDoubleTensorSingleFunctorObjIso (hX : ObjectProperty.flat X)
    (hY : ObjectProperty.flat Y) (N : C) :
    Q.obj (double g h) ⊗ (singleFunctor C 0).obj N ≅ Q.obj (double (g ▷ N) h) :=
  haveI := CochainComplex.isStrictlyGE_double g h
  haveI := CochainComplex.isStrictlyLE_double g h
  QObjTensorSingleFunctorObjIso _
      (CochainComplex.kFlat_of_bounded_of_flat _ i₀ i₁ (flat_double_X g h hX hY)) N ≪≫
    Q.mapIso (mapHomologicalComplexObjDoubleIso g h (by have h' : i₀ + 1 = i₁ := h; omega)
      (tensorRight N))


section Tor

variable (P : ObjectProperty C)

/-- The derived tensor product of `A[0]` and `B[0]` has cohomology objects in `P`, concentrated
in degrees `-1` and `0`: the objects `Tor₁(A, B)` and `A ⊗ B` lie in `P`, and the higher `Tor`
vanish. -/
def TorConcentrated (A B : C) : Prop :=
  ∀ n : ℤ,
    P ((homologyFunctor C n).obj ((singleFunctor C 0).obj A ⊗ (singleFunctor C 0).obj B)) ∧
      ((n < -1 ∨ 0 < n) → IsZero ((homologyFunctor C n).obj
        ((singleFunctor C 0).obj A ⊗ (singleFunctor C 0).obj B)))

variable {P} [P.IsClosedUnderIsomorphisms]

/-- `TorConcentrated P` is invariant under isomorphisms in both variables. -/
lemma TorConcentrated.of_iso {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (h : TorConcentrated P A B) : TorConcentrated P A' B' := fun n ↦
  let e := (homologyFunctor C n).mapIso
    (tensorIso ((singleFunctor C 0).mapIso eA) ((singleFunctor C 0).mapIso eB))
  ⟨P.prop_of_iso e (h n).1, fun hn ↦ ((h n).2 hn).of_iso e.symm⟩

/-- `TorConcentrated P` is symmetric, the derived tensor product being symmetric. -/
lemma TorConcentrated.symm {A B : C} (h : TorConcentrated P A B) : TorConcentrated P B A := by
  obtain ⟨_⟩ := nonempty_braidedCategory C
  intro n
  let e := (homologyFunctor C n).mapIso
    (β_ ((singleFunctor C 0).obj A) ((singleFunctor C 0).obj B))
  exact ⟨P.prop_of_iso e (h n).1, fun hn ↦ ((h n).2 hn).of_iso e.symm⟩

omit [P.IsClosedUnderIsomorphisms] in
/-- `Tor` of a zero object with anything vanishes. -/
lemma TorConcentrated.of_isZero_left (h0 : ∀ X : C, IsZero X → P X) {A : C} (hA : IsZero A)
    (B : C) : TorConcentrated P A B := fun n ↦
  have h : IsZero ((homologyFunctor C n).obj
      ((singleFunctor C 0).obj A ⊗ (singleFunctor C 0).obj B)) :=
    (homologyFunctor C n).map_isZero ((tensorRight ((singleFunctor C 0).obj B)).map_isZero
      ((singleFunctor C 0).map_isZero hA))
  ⟨h0 _ h, fun _ ↦ h⟩

/-- `TorConcentrated P` is stable under binary biproducts in the first variable, if `P` is. -/
lemma TorConcentrated.biprod_left (h2 : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) {A A' B : C}
    (h : TorConcentrated P A B) (h' : TorConcentrated P A' B) :
    TorConcentrated P (A ⊞ A') B := fun n ↦ by
  let F := singleFunctor C 0 ⋙ tensorRight ((singleFunctor C 0).obj B) ⋙ homologyFunctor C n
  have := preservesBinaryBiproducts_of_preservesBiproducts F
  let e : F.obj (A ⊞ A') ≅ F.obj A ⊞ F.obj A' := F.mapBiprod A A'
  refine ⟨P.prop_of_iso e.symm (h2 _ _ (h n).1 (h' n).1), fun hn ↦ ?_⟩
  refine IsZero.of_iso ?_ e
  rw [IsZero.iff_id_eq_zero]
  ext <;> simp [((h n).2 hn).eq_of_src _ 0, ((h' n).2 hn).eq_of_src _ 0]

/-- `TorConcentrated P` is stable under finite biproducts in the first variable. -/
lemma TorConcentrated.biproduct_left [HasFiniteBiproducts C] (h0 : ∀ X : C, IsZero X → P X)
    (h2 : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) {k : ℕ} (A : Fin k → C) {B : C}
    (h : ∀ j, TorConcentrated P (A j) B) : TorConcentrated P (⨁ A) B :=
  prop_biproduct_of_forall (fun A ↦ TorConcentrated P A B)
    (fun e h ↦ h.of_iso e (Iso.refl B))
    (fun _ hX ↦ .of_isZero_left h0 hX B) (fun _ _ h h' ↦ h.biprod_left h2 h') A h

/-- The derived tensor product of the unit with `B[0]` is `B[0]`. -/
noncomputable def singleFunctorUnitTensorIso (B : C) :
    (singleFunctor C 0).obj (𝟙_ C) ⊗ (singleFunctor C 0).obj B ≅ (singleFunctor C 0).obj B :=
  whiskerRightIso (singleFunctorObjUnitIso C) _ ≪≫ λ_ _

/-- `Tor` of the unit and `B` is `B` in degree `0`. -/
lemma TorConcentrated.unit_left (h0 : ∀ X : C, IsZero X → P X) {B : C} (hB : P B) :
    TorConcentrated P (𝟙_ C) B := fun n ↦ by
  let e := (homologyFunctor C n).mapIso (singleFunctorUnitTensorIso B)
  by_cases hn : n = 0
  · subst hn
    exact ⟨P.prop_of_iso (((singleFunctorCompHomologyFunctorIso C 0).app B).symm ≪≫ e.symm) hB,
      fun hn ↦ by omega⟩
  · have hz : IsZero ((homologyFunctor C n).obj ((singleFunctor C 0).obj B)) := by
      obtain hn | hn := lt_or_gt_of_ne hn
      · exact ((singleFunctor C 0).obj B).isZero_of_isGE 0 n hn
      · exact ((singleFunctor C 0).obj B).isZero_of_isLE 0 n hn
    exact ⟨h0 _ (hz.of_iso e), fun _ ↦ hz.of_iso e⟩

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [MonoidalPreadditive C] [HasDerivedCategory.{v} C]
  [Abelian.HasFunctorialFlatResolution C] in
/-- The unit of a closed braided monoidal category is flat. -/
lemma flat_tensorUnit : ObjectProperty.flat (𝟙_ C) :=
  ObjectProperty.flat_of_isDualizable ⟨inferInstance⟩

/-- If `g : 𝟙 ⟶ 𝟙` is a monomorphism acting by zero on `N`, then `Tor₁(coker g, N)` and
`coker g ⊗ N` are both `N`, and the higher `Tor` vanish. -/
lemma TorConcentrated.cokernel_left (h0 : ∀ X : C, IsZero X → P X) (g : 𝟙_ C ⟶ 𝟙_ C) [Mono g]
    {N : C} (hgN : g ▷ N = 0) (hN : P N) : TorConcentrated P (cokernel g) N := fun n ↦ by
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  obtain ⟨e₁⟩ := nonempty_Q_obj_double_iso_singleFunctor_obj_cokernel g hrel
  let e : (homologyFunctor C n).obj
      ((singleFunctor C 0).obj (cokernel g) ⊗ (singleFunctor C 0).obj N) ≅
      (double (g ▷ N) hrel).homology n :=
    (homologyFunctor C n).mapIso (whiskerRightIso e₁.symm _ ≪≫
      QObjDoubleTensorSingleFunctorObjIso g hrel flat_tensorUnit flat_tensorUnit N) ≪≫
      (homologyFunctorFactors C n).app _
  have hP : P (𝟙_ C ⊗ N) := P.prop_of_iso (λ_ N).symm hN
  by_cases hn₀ : n = -1
  · subst hn₀
    refine ⟨P.prop_of_iso (e ≪≫ CochainComplex.doubleHomologyIso₀ _ hrel ≪≫
      kernel.mapIso _ 0 (Iso.refl _) (Iso.refl _) (by simp [hgN]) ≪≫ kernelZeroIsoSource).symm hP,
      fun h ↦ by omega⟩
  by_cases hn₁ : n = 0
  · subst hn₁
    refine ⟨P.prop_of_iso (e ≪≫ CochainComplex.doubleHomologyIso₁ _ hrel ≪≫
      cokernel.mapIso _ 0 (Iso.refl _) (Iso.refl _) (by simp [hgN]) ≪≫
      cokernelZeroIsoTarget).symm hP, fun h ↦ by omega⟩
  have hz := (CochainComplex.isZero_double_homology (g ▷ N) hrel hn₀ hn₁).of_iso e
  exact ⟨h0 _ hz, fun _ ↦ hz⟩

/-- **`Tor` of constant modules.** Let `g a : 𝟙 ⟶ 𝟙` (`a : ℕ`) be monomorphisms such that `g a`
acts by zero on `coker (g b)` for `b ≤ a`, and such that `P` contains the unit and the cokernels
of the `g a`. Then the derived tensor product of two objects `⊕ⱼ coker (g (e j)) ⊕ 𝟙ʳ` placed
in degree `0` has cohomology objects in `P`, concentrated in degrees `-1` and `0`. -/
theorem torConcentrated_biprod_cokernel_unit [HasFiniteBiproducts C]
    (h0 : ∀ X : C, IsZero X → P X) (h2 : ∀ X Y : C, P X → P Y → P (X ⊞ Y))
    (g : ℕ → (𝟙_ C ⟶ 𝟙_ C)) [∀ a, Mono (g a)] (hg : ∀ a b, b ≤ a → g a ▷ cokernel (g b) = 0)
    (hc : ∀ a, P (cokernel (g a))) (h1 : P (𝟙_ C)) {k r k' r' : ℕ} (e : Fin k → ℕ)
    (e' : Fin k' → ℕ) :
    TorConcentrated P ((⨁ fun j ↦ cokernel (g (e j))) ⊞ ⨁ fun _ : Fin r ↦ 𝟙_ C)
      ((⨁ fun j ↦ cokernel (g (e' j))) ⊞ ⨁ fun _ : Fin r' ↦ 𝟙_ C) := by
  have hcc (a b : ℕ) : TorConcentrated P (cokernel (g a)) (cokernel (g b)) := by
    obtain hab | hab := le_total b a
    · exact .cokernel_left h0 (g a) (hg a b hab) (hc b)
    · exact (TorConcentrated.cokernel_left h0 (g b) (hg b a hab) (hc a)).symm
  have hconst {k r : ℕ} (e : Fin k → ℕ) {B : C}
      (hcB : ∀ a, TorConcentrated P (cokernel (g a)) B) (h1B : TorConcentrated P (𝟙_ C) B) :
      TorConcentrated P ((⨁ fun j ↦ cokernel (g (e j))) ⊞ ⨁ fun _ : Fin r ↦ 𝟙_ C) B :=
    (TorConcentrated.biproduct_left h0 h2 _ fun j ↦ hcB (e j)).biprod_left h2
      (TorConcentrated.biproduct_left h0 h2 _ fun _ ↦ h1B)
  refine hconst e (fun a ↦ (hconst e' (fun b ↦ hcc b a) (.unit_left h0 (hc a))).symm) ?_
  exact (hconst e' (fun b ↦ (TorConcentrated.unit_left h0 (hc b)).symm)
    (.unit_left h0 h1)).symm

end Tor

section Dual

/-- **The dual of a two-term complex.** For a monomorphism `g : X ⟶ Y` between objects with right
duals, `coker(g)[q]` has a bounded left dual `D`, the two-term complex `Yᘁ --±gᘁ--> Xᘁ` in degrees
`-q`, `-q + 1`. -/
theorem exists_exactPairing_singleFunctor_cokernel {X Y : C} [HasRightDual X] [HasRightDual Y]
    (g : X ⟶ Y) [Mono g] (q : ℤ) :
    ∃ (D : DerivedCategory C) (u : ℤˣ), TStructure.t.bounded D ∧
      (∀ n, n ≠ -q → n ≠ -q + 1 → IsZero ((homologyFunctor C n).obj D)) ∧
      Nonempty ((homologyFunctor C (-q)).obj D ≅ kernel (u • gᘁ)) ∧
      Nonempty ((homologyFunctor C (-q + 1)).obj D ≅ cokernel (u • gᘁ)) ∧
      Nonempty (ExactPairing D ((singleFunctor C q).obj (cokernel g))) := by
  have hrel : (ComplexShape.up ℤ).Rel (-(-q + 1)) (-(-q)) := by simp
  have hne : -(-q + 1) ≠ -(-q) := by omega
  let K : CochainComplex C ℤ := double g hrel
  have hK (n : ℤ) : IsDualizable (K.X n) := by
    by_cases h₀ : n = -(-q + 1)
    · subst h₀
      exact IsDualizable.of_iso (doubleXIso₀ g hrel).symm ⟨inferInstance⟩
    by_cases h₁ : n = -(-q)
    · subst h₁
      exact IsDualizable.of_iso (doubleXIso₁ g hrel hne).symm ⟨inferInstance⟩
    exact IsZero.isDualizable (isZero_double_X g hrel n h₀ h₁)
  let _ (n : ℤ) : HasRightDual (K.X n) := (hK n).some
  have := CochainComplex.isStrictlyGE_double g hrel
  have := CochainComplex.isStrictlyLE_double g hrel
  obtain ⟨_⟩ := nonempty_exactPairing_Q_obj K (-(-q + 1)) (-(-q))
  obtain ⟨_⟩ := nonempty_braidedCategory C
  obtain ⟨eK⟩ := nonempty_Q_obj_double_iso_singleFunctor_obj_cokernel g hrel
  let A := rightAdjointMateIso (doubleXIso₁ g hrel hne)
  let B := rightAdjointMateIso (doubleXIso₀ g hrel)
  let u := (-q + 1).negOnePow
  have hd : K.rightDual.d (-q) (-q + 1) = A.inv ≫ (u • gᘁ) ≫ B.hom := by
    rw [CochainComplex.rightDual_d, double_d g hrel hne, comp_rightAdjointMate,
      comp_rightAdjointMate]
    simp [A, B, u, Linear.comp_units_smul, Linear.units_smul_comp]
  have hz (n : ℤ) (h₀ : n ≠ -q) (h₁ : n ≠ -q + 1) : IsZero (K.rightDual.X n) :=
    CochainComplex.rightDual.isZero_X K n (isZero_double_X g hrel _ (by omega) (by omega))
  let eH (n : ℤ) := (homologyFunctorFactors C n).app K.rightDual
  refine ⟨Q.obj K.rightDual, u, ?_, fun n h₀ h₁ ↦ ?_, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · rw [← exists_homologyConcentratedIn_iff_bounded]
    exact ⟨-(-(-q)), -(-(-q + 1)), (inferInstance : (Q.obj K.rightDual).IsGE (-(-(-q)))),
      (inferInstance : (Q.obj K.rightDual).IsLE (-(-(-q + 1))))⟩
  · exact (ShortComplex.isZero_homology_of_isZero_X₂ _ (hz n h₀ h₁)).of_iso (eH n)
  · exact eH (-q) ≪≫
      CochainComplex.homologyIsoKernel _ (-q) (-q + 1) rfl (hz _ (by omega) (by omega)) ≪≫
      kernel.mapIso _ _ A.symm B.symm (by simp [hd])
  · exact eH (-q + 1) ≪≫
      CochainComplex.homologyIsoCokernel _ (-q) (-q + 1) rfl (hz _ (by omega) (by omega)) ≪≫
      cokernel.mapIso _ _ A.symm B.symm (by simp [hd])
  · let _ := BraidedCategory.exactPairing_swap (Q.obj K) (Q.obj K.rightDual)
    exact exactPairingCongr (Iso.refl _) (eqToIso (by rw [neg_neg]) ≪≫ eK.symm)

end Dual

section BoundedDual

variable (P : ObjectProperty C)

/-- An object `M` of `D(C)` has a left dual `D` with cohomology concentrated in degrees
`[a, b]`, whose cohomology objects lie in `P`. -/
def HasBoundedDual (a b : ℤ) (M : DerivedCategory C) : Prop :=
  ∃ D : DerivedCategory C, D.IsGE a ∧ D.IsLE b ∧ (∀ n, P ((homologyFunctor C n).obj D)) ∧
    Nonempty (ExactPairing D M)

variable {P}

/-- Having a bounded left dual with cohomology objects in `P` is invariant under isomorphisms. -/
lemma HasBoundedDual.of_iso {a b : ℤ} {M M' : DerivedCategory C} (e : M ≅ M')
    (h : HasBoundedDual P a b M) : HasBoundedDual P a b M' := by
  obtain ⟨D, ha, hb, hP, ⟨_⟩⟩ := h
  exact ⟨D, ha, hb, hP, ⟨exactPairingCongr (Iso.refl _) e.symm⟩⟩

/-- A zero object has itself as bounded left dual. -/
lemma HasBoundedDual.of_isZero (h0 : ∀ X : C, IsZero X → P X) {a b : ℤ} {M : DerivedCategory C}
    (hM : IsZero M) : HasBoundedDual P a b M := by
  have hH (n : ℤ) : IsZero ((homologyFunctor C n).obj M) := (homologyFunctor C n).map_isZero hM
  exact ⟨M, (isGE_iff M a).2 fun i _ ↦ hH i, (isLE_iff M b).2 fun i _ ↦ hH i,
    fun n ↦ h0 _ (hH n), ⟨exactPairingOfIsZero hM⟩⟩

/-- Having a bounded left dual with cohomology objects in `P` is stable under binary biproducts,
if `P` is. -/
lemma HasBoundedDual.biprod [P.IsClosedUnderIsomorphisms]
    (h2 : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) {a b : ℤ} {M M' : DerivedCategory C}
    (h : HasBoundedDual P a b M) (h' : HasBoundedDual P a b M') :
    HasBoundedDual P a b (M ⊞ M') := by
  obtain ⟨D, ha, hb, hP, ⟨_⟩⟩ := h
  obtain ⟨D', ha', hb', hP', ⟨_⟩⟩ := h'
  let _ : HasRightDual D := ⟨M⟩
  let _ : HasRightDual D' := ⟨M'⟩
  have (n : ℤ) := preservesBinaryBiproducts_of_preservesBiproducts (homologyFunctor C n)
  refine ⟨D ⊞ D', (isGE_iff _ _).2 fun i hi ↦ ?_, (isLE_iff _ _).2 fun i hi ↦ ?_,
    fun n ↦ P.prop_of_iso ((homologyFunctor C n).mapBiprod D D').symm
      (h2 _ _ (hP n) (hP' n)), ⟨exactPairingBiprod D D'⟩⟩
  · exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨D.isZero_of_isGE a i hi,
      D'.isZero_of_isGE a i hi⟩) ((homologyFunctor C i).mapBiprod D D')
  · exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨D.isZero_of_isLE b i hi,
      D'.isZero_of_isLE b i hi⟩) ((homologyFunctor C i).mapBiprod D D')

/-- The unit placed in degree `q` has a left dual concentrated in degrees `[-q, -q + 1]` whose
cohomology objects lie in `P`, provided `P` contains the unit and the zero objects. -/
lemma hasBoundedDual_singleFunctor_tensorUnit [P.IsClosedUnderIsomorphisms]
    (h0 : ∀ X : C, IsZero X → P X) (h1 : P (𝟙_ C)) (q : ℤ) :
    HasBoundedDual P (-q) (-q + 1) ((singleFunctor C q).obj (𝟙_ C)) := by
  let _ : HasRightDual (0 : C) := { rightDual := 0, exact := exactPairingOfIsZero (isZero_zero C) }
  obtain ⟨D, u, -, hz, ⟨e₀⟩, ⟨e₁⟩, ⟨_⟩⟩ :=
    exists_exactPairing_singleFunctor_cokernel (0 : (0 : C) ⟶ 𝟙_ C) q
  have hP (n : ℤ) : P ((homologyFunctor C n).obj D) := by
    by_cases h₀ : n = -q
    · subst h₀
      exact P.prop_of_iso (e₀ ≪≫ kernel.mapIso _ (0 : (𝟙_ C)ᘁ ⟶ (0 : C)ᘁ) (Iso.refl _)
        (Iso.refl _) (by simp [(isZero_zero C).eq_of_tgt (u • (0 : (0 : C) ⟶ 𝟙_ C)ᘁ) 0]) ≪≫
        kernelZeroIsoSource).symm h1
    by_cases h₁ : n = -q + 1
    · subst h₁
      have := (isZero_zero C).epi (u • (0 : (0 : C) ⟶ 𝟙_ C)ᘁ)
      exact h0 _ ((isZero_cokernel_of_epi _).of_iso e₁)
    exact h0 _ (hz n h₀ h₁)
  exact HasBoundedDual.of_iso
    ((singleFunctor C q).mapIso (cokernelZeroIsoTarget (X := (0 : C)) (Y := 𝟙_ C)))
    ⟨D, (isGE_iff D _).2 fun i hi ↦ hz i (by omega) (by omega),
      (isLE_iff D _).2 fun i hi ↦ hz i (by omega) (by omega), hP, ⟨inferInstance⟩⟩

/-- For a monomorphism `g : 𝟙 ⟶ 𝟙`, the cokernel of `g` placed in degree `q` has a left dual
concentrated in degrees `[-q, -q + 1]` whose cohomology objects lie in `P`, provided `P` contains
the zero objects and the cokernels of all endomorphisms of the unit. -/
lemma hasBoundedDual_singleFunctor_cokernel [P.IsClosedUnderIsomorphisms]
    (h0 : ∀ X : C, IsZero X → P X) (hc : ∀ f : 𝟙_ C ⟶ 𝟙_ C, P (cokernel f))
    (g : 𝟙_ C ⟶ 𝟙_ C) [Mono g] (q : ℤ) :
    HasBoundedDual P (-q) (-q + 1) ((singleFunctor C q).obj (cokernel g)) := by
  obtain ⟨D, u, -, hz, ⟨e₀⟩, ⟨e₁⟩, ⟨_⟩⟩ := exists_exactPairing_singleFunctor_cokernel g q
  rw [rightAdjointMate_tensorUnit] at e₀ e₁
  refine ⟨D, (isGE_iff D _).2 fun i hi ↦ hz i (by omega) (by omega),
    (isLE_iff D _).2 fun i hi ↦ hz i (by omega) (by omega), fun n ↦ ?_, ⟨inferInstance⟩⟩
  by_cases h₀ : n = -q
  · subst h₀
    have : IsIso (u • 𝟙 (𝟙_ C)) := ⟨u⁻¹ • 𝟙 _, by simp [smul_smul], by simp [smul_smul]⟩
    have : Mono (u • g) := by
      rw [show u • g = g ≫ (u • 𝟙 (𝟙_ C)) by rw [Linear.comp_units_smul, Category.comp_id]]
      infer_instance
    exact h0 _ ((isZero_kernel_of_mono _).of_iso e₀)
  by_cases h₁ : n = -q + 1
  · subst h₁
    exact P.prop_of_iso e₁.symm (hc _)
  exact h0 _ (hz n h₀ h₁)

/-- **Duals of constant objects.** For monomorphisms `g a : 𝟙 ⟶ 𝟙`, an object
`⊕ⱼ coker (g (e j)) ⊕ 𝟙ʳ` placed in degree `q` has a left dual concentrated in degrees
`[-q, -q + 1]` whose cohomology objects lie in `P`, provided `P` contains the zero objects, the
unit, the cokernels of all endomorphisms of the unit, and is stable under binary biproducts. -/
theorem hasBoundedDual_singleFunctor_biprod_cokernel_unit [HasFiniteBiproducts C]
    [P.IsClosedUnderIsomorphisms] (h0 : ∀ X : C, IsZero X → P X)
    (h2 : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) (hc : ∀ f : 𝟙_ C ⟶ 𝟙_ C, P (cokernel f))
    (h1 : P (𝟙_ C)) (g : ℕ → (𝟙_ C ⟶ 𝟙_ C)) [∀ a, Mono (g a)] {k r : ℕ} (e : Fin k → ℕ)
    (q : ℤ) :
    HasBoundedDual P (-q) (-q + 1) ((singleFunctor C q).obj
      ((⨁ fun j ↦ cokernel (g (e j))) ⊞ ⨁ fun _ : Fin r ↦ 𝟙_ C)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (singleFunctor C q)
  have hfin {k : ℕ} (A : Fin k → C)
      (hA : ∀ j, HasBoundedDual P (-q) (-q + 1) ((singleFunctor C q).obj (A j))) :
      HasBoundedDual P (-q) (-q + 1) ((singleFunctor C q).obj (⨁ A)) :=
    HasBoundedDual.of_iso ((singleFunctor C q).mapBiproduct A).symm
      (prop_biproduct_of_forall (HasBoundedDual P (-q) (-q + 1)) (fun e h ↦ h.of_iso e)
        (fun _ h ↦ .of_isZero h0 h)
        (fun _ _ h h' ↦ h.biprod h2 h') _ hA)
  exact HasBoundedDual.of_iso ((singleFunctor C q).mapBiprod _ _).symm (HasBoundedDual.biprod h2
    (hfin _ fun j ↦ hasBoundedDual_singleFunctor_cokernel h0 hc (g (e j)) q)
    (hfin _ fun _ ↦ hasBoundedDual_singleFunctor_tensorUnit h0 h1 q))

end BoundedDual

end DerivedCategory
