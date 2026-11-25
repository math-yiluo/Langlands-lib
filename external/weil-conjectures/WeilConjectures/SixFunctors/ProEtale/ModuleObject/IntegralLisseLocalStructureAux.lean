/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Auxiliary results: lisse `𝒪_E`-sheaves are locally constant

This file proves the inputs of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure`
(Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8).

* Block matrices: a map of finite biproducts whose pivot divides its row and its column is,
  up to elementary row and column operations, `p ⊕ s` (`CategoryTheory.Limits.biprod_block_eq`,
  `CategoryTheory.Limits.finiteBiproduct_pivot_block`).
* Constant modules: for a condensed ring `Λ` and global sections `s₁, …, s_k` of `Λ`, the
  constant module `⊕ⱼ Λ_X/sⱼ ⊕ Λ_X^r` (`ProEtale.CondensedRing.constModule`) is stable under
  pullback (`ProEtale.CondensedRing.upperStarConstModuleIso`).
* The integral pivot: for the integral coefficient ring `𝒪_{E,X}` of a normed finite extension
  `E` of `ℚ_ℓ`, a map from a finite free to a free module whose rational cokernel is locally free
  is locally either zero, or splits off a summand `𝒪/ϖ^e`
  (`ProEtale.CondensedRing.integralMatrix_pivot_cover_pow`).
* By strong induction, its cokernel is locally a constant module
  (`ProEtale.CondensedRing.exists_cover_isIntegralConstModule_of_presentation`), and so is every
  locally finitely presented module on a scheme with noetherian underlying space
  (`ProEtale.CondensedRing.lfpLocallyConstModule_integralCoeff`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The elementary column operation `(x, y) ↦ (x + r y, y)` on `A ⊞ A₁`, as an automorphism. -/
@[simps]
noncomputable def biprodColumnOpIso {A A₁ : C} (r : A₁ ⟶ A) : A ⊞ A₁ ≅ A ⊞ A₁ where
  hom := biprod.lift (biprod.desc (𝟙 A) r) (biprod.desc 0 (𝟙 A₁))
  inv := biprod.lift (biprod.desc (𝟙 A) (-r)) (biprod.desc 0 (𝟙 A₁))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- The elementary row operation `(x, y) ↦ (x, c x + y)` on `B ⊞ B₁`, as an automorphism. -/
@[simps]
noncomputable def biprodRowOpIso {B B₁ : C} (c : B ⟶ B₁) : B ⊞ B₁ ≅ B ⊞ B₁ where
  hom := biprod.lift (biprod.desc (𝟙 B) 0) (biprod.desc c (𝟙 B₁))
  inv := biprod.lift (biprod.desc (𝟙 B) 0) (biprod.desc (-c) (𝟙 B₁))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- A block matrix whose corner `p` divides its first row and its first column is, up to
elementary row and column operations, the diagonal block matrix
`biprod.map p (d - r ≫ p ≫ c)`. -/
lemma biprod_block_eq {A A₁ B B₁ : C} (p : A ⟶ B) (r : A₁ ⟶ A) (c : B ⟶ B₁)
    (d : A₁ ⟶ B₁) :
    biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc (p ≫ c) d) =
      (biprodColumnOpIso r).hom ≫ biprod.map p (d - r ≫ p ≫ c) ≫ (biprodRowOpIso c).hom := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [biprodColumnOpIso_hom, biprodRowOpIso_hom, biprod.lift_eq, biprod.desc_eq,
      biprod.map_eq, Preadditive.comp_add, Preadditive.add_comp, Preadditive.sub_comp,
      Preadditive.comp_sub]

end Preadditive

section Cokernel

variable [Preadditive C] [HasBinaryBiproducts C] [HasCokernels C]

/-- The cokernel of a diagonal map `f ⊞ g` is the biproduct of the cokernels. -/
private noncomputable def cokernelBiprodMapIso {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π g)) (by
    apply biprod.hom_ext' <;> simp)
  inv := biprod.desc
    (cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inl_map_assoc, cokernel.condition, comp_zero]))
    (cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inr_map_assoc, cokernel.condition, comp_zero]))
  hom_inv_id := by
    apply coequalizer.hom_ext
    apply biprod.hom_ext' <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply coequalizer.hom_ext <;> simp

/-- The cokernel of a block matrix whose corner `p` divides its first row and column. -/
private noncomputable def cokernelBiprodBlockIso {A A₁ B B₁ : C} (p : A ⟶ B) (r : A₁ ⟶ A)
    (c : B ⟶ B₁) (d : A₁ ⟶ B₁) :
    cokernel (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc (p ≫ c) d)) ≅
      cokernel p ⊞ cokernel (d - r ≫ p ≫ c) :=
  cokernelIsoOfEq (biprod_block_eq p r c d) ≪≫ cokernelEpiComp _ _ ≪≫
    cokernelCompIsIso _ _ ≪≫ cokernelBiprodMapIso _ _

end Cokernel

section FiniteBiproduct

variable [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]

/-- Prepending a summand `G e₀` to a biproduct `⨁ⱼ G (eⱼ)` indexed by `Fin k`. -/
noncomputable def biprodBiproductConsIso (G : ℕ → C) {k : ℕ} (e₀ : ℕ) (e : Fin k → ℕ)
    (F : C) :
    G e₀ ⊞ ((⨁ fun j ↦ G (e j)) ⊞ F) ≅
      (⨁ fun j ↦ G ((Fin.cons e₀ e : Fin (k + 1) → ℕ) j)) ⊞ F :=
  (biprod.associator _ _ _).symm ≪≫
    biprod.mapIso
      (biprod.mapIso
        (eqToIso (congrArg G (Fin.cons_zero (α := fun _ : Fin (k + 1) ↦ ℕ) e₀ e).symm))
        (biproduct.mapIso fun i ↦
          eqToIso (congrArg G (Fin.cons_succ (α := fun _ : Fin (k + 1) ↦ ℕ) e₀ e i).symm)) ≪≫
        (biproductFinSuccIso fun j ↦ G ((Fin.cons e₀ e : Fin (k + 1) → ℕ) j)).symm)
      (Iso.refl F)

/-- Splitting a constant finite biproduct at the index `j` into the summand `j` and the
remaining summands. -/
noncomputable def finiteBiproductSplitIso (P : C) {n : ℕ} (j : Fin (n + 1)) :
    (⨁ fun _ : Fin (n + 1) ↦ P) ≅ P ⊞ (⨁ fun _ : Fin n ↦ P) where
  hom := biprod.lift (biproduct.π (fun _ : Fin (n + 1) ↦ P) j)
    (biproduct.lift fun k ↦ biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k))
  inv := biprod.desc (biproduct.ι (fun _ : Fin (n + 1) ↦ P) j)
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : Fin (n + 1) ↦ P) (j.succAbove k))
  hom_inv_id := by
    have h₀ : biproduct.ι (fun _ : Fin (n + 1) ↦ P) j ≫
        (biproduct.lift fun k : Fin n ↦
          biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k)) = 0 := by
      apply biproduct.hom_ext
      intro k
      simp
    have h₁ (i : Fin n) : biproduct.ι (fun _ : Fin (n + 1) ↦ P) (j.succAbove i) ≫
        (biproduct.lift fun k : Fin n ↦
          biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k)) =
        biproduct.ι (fun _ : Fin n ↦ P) i := by
      apply biproduct.hom_ext
      intro k
      by_cases h : i = k
      · subst k
        simp
      · simp [h, Fin.succAbove_right_injective.ne h]
    apply biproduct.hom_ext'
    intro i
    induction i using j.succAboveCases with
    | x => simp [biprod.lift_desc, Preadditive.comp_add, reassoc_of% h₀]
    | p i => simp [biprod.lift_desc, Preadditive.comp_add, reassoc_of% h₁, Fin.succAbove_ne]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext
      intro i
      simp
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro i
      apply biproduct.hom_ext
      intro k
      by_cases h : i = k
      · subst k
        simp
      · simp [h, Fin.succAbove_right_injective.ne h]

/-- A map of constant finite biproducts whose `(i, j)` entry `p` divides every entry of its row
and of its column is, after splitting off the summands `j` and `i`, a block matrix
`((p, r ≫ p), (p ≫ c, d))`. -/
theorem finiteBiproduct_pivot_block {P : C} {n t : ℕ}
    (f : (⨁ fun _ : Fin n ↦ P) ⟶ ⨁ fun _ : Fin t ↦ P) (i : Fin t) (j : Fin n)
    (p : P ⟶ P) (hp : p = biproduct.ι (fun _ : Fin n ↦ P) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) i)
    (q : Fin n → (P ⟶ P))
    (hq : ∀ k, q k ≫ p = biproduct.ι (fun _ : Fin n ↦ P) k ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) i)
    (q' : Fin t → (P ⟶ P))
    (hq' : ∀ k, p ≫ q' k = biproduct.ι (fun _ : Fin n ↦ P) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) k) :
    ∃ (m s : ℕ), m < n ∧
      ∃ (eA : (⨁ fun _ : Fin n ↦ P) ≅ P ⊞ (⨁ fun _ : Fin m ↦ P))
        (eB : (⨁ fun _ : Fin t ↦ P) ≅ P ⊞ (⨁ fun _ : Fin s ↦ P))
        (r : (⨁ fun _ : Fin m ↦ P) ⟶ P) (c : P ⟶ ⨁ fun _ : Fin s ↦ P)
        (d : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin s ↦ P),
        eA.inv ≫ f ≫ eB.hom = biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc (p ≫ c) d) := by
  subst hp
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    cases t with
    | zero => exact Fin.elim0 i
    | succ s =>
      let eA := finiteBiproductSplitIso P j
      let eB := finiteBiproductSplitIso P i
      let b := eA.inv ≫ f ≫ eB.hom
      refine ⟨m, s, Nat.lt_succ_self m, eA, eB, biproduct.desc fun k ↦ q (j.succAbove k),
        biproduct.lift fun k ↦ q' (i.succAbove k), biprod.inr ≫ b ≫ biprod.snd, ?_⟩
      apply biprod.hom_ext' <;> apply biprod.hom_ext
      · simp [b, eA, eB, finiteBiproductSplitIso]
      · apply biproduct.hom_ext
        intro k
        simpa [b, eA, eB, finiteBiproductSplitIso] using (hq' (i.succAbove k)).symm
      · apply biproduct.hom_ext'
        intro k
        simpa [b, eA, eB, finiteBiproductSplitIso, Category.assoc] using
          (hq (j.succAbove k)).symm
      · simp [b]

end FiniteBiproduct

end CategoryTheory.Limits

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- On the regular module of a commutative monoid object, the multiplication by a global
section `σ` is the action of `σ`. -/
private lemma regularLift_regular_hom_eq_globalSmul [BraidedCategory C] {R : C} [MonObj R]
    [IsCommMonObj R] (σ : 𝟙_ C ⟶ R) :
    (regularLift (regular R) σ).hom = globalSmul σ (regular R) := by
  have key : (λ_ R).inv ≫ σ ▷ R ≫ μ[R] = (ρ_ R).inv ≫ R ◁ σ ≫ μ[R] := by
    conv_lhs => rw [← IsCommMonObj.mul_comm R]
    rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc]
  exact key.symm

/-- The image under a lax monoidal functor of the multiplication by a global section. -/
private lemma regularLift_regular_obj_hom {D : Type*} [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (c : 𝟙_ C ⟶ A) :
    (regularLift (regular (F.obj A)) (Functor.LaxMonoidal.ε F ≫ F.map c)).hom =
      F.map (regularLift (regular A) c).hom := by
  have hact : act (regular (F.obj A)).X = Functor.LaxMonoidal.μ F A A ≫ F.map μ[A] := rfl
  have hact' : act (regular A).X = μ[A] := rfl
  simp only [regularLift, homMk_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.map_comp, hact, hact', Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]

/-- The action of a global section on the regular module is invariant under isomorphisms of
monoid objects. -/
lemma globalSmul_comp_regular_of_isIso {A B : C} [MonObj A] [MonObj B] (e : A ⟶ B) [IsIso e]
    [IsMonHom e] (σ : 𝟙_ C ⟶ A) :
    globalSmul (σ ≫ e) (regular B) = inv e ≫ globalSmul σ (regular A) ≫ e := by
  change (λ_ B).inv ≫ (σ ≫ e) ▷ B ≫ μ[B] = inv e ≫ ((λ_ A).inv ≫ σ ▷ A ≫ μ[A]) ≫ e
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def,
    Category.assoc, leftUnitor_inv_naturality_assoc, ← comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, IsIso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The action of a global section on the image of the regular module under `mapMod` is its action
on the regular module of the image monoid object. -/
lemma globalSmul_mapMod_regular {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {R : C} [MonObj R] (σ : 𝟙_ D ⟶ F.obj R) :
    globalSmul σ ((F.mapMod R).obj (regular R)) = globalSmul σ (regular (F.obj R)) :=
  rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The multiplication by the image `p_X^* s` of a global section `s` of `Λ`, as an endomorphism
of the regular `Λ_X`-module. -/
noncomputable def constRegularEnd (X : Scheme.{u})
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    Mod.regular (condensedRingObj Λ X) ⟶ Mod.regular (condensedRingObj Λ X) :=
  Mod.regularLift (Mod.regular _)
    (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s)

/-- The underlying morphism of the multiplication by a constant global section is the action of
the global section on the regular module. -/
lemma constRegularEnd_hom (X : Scheme.{u})
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    (constRegularEnd Λ X s).hom = Mod.globalSmul
      (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s)
      (Mod.regular (condensedRingObj Λ X)) :=
  Mod.regularLift_regular_hom_eq_globalSmul _

/-- The pullback of `Λ_X`-modules along `g`, normalized by the inverse of the coefficient
comparison `α_g : g^* Λ_X ≅ Λ_Y` instead of extension of scalars along it. -/
noncomputable abbrev normalizedUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  (ProEtale.upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ X) ⋙
    Mod.comap (inv (condensedPullbackHom Λ g))

/-- The pullback `g^*` on module objects is the normalized pullback. -/
noncomputable def upperStarIsoNormalizedUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (g)^*⟦Λ⟧ ≅ normalizedUpperStar Λ g :=
  Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g))

/-- The normalized pullback of the regular module is the regular module. -/
noncomputable def normalizedUpperStarRegularIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (normalizedUpperStar Λ g).obj (Mod.regular (condensedRingObj Λ X)) ≅
      Mod.regular (condensedRingObj Λ Y) :=
  Mod.isoMk (asIso (condensedPullbackHom Λ g)) (by
    change (inv (condensedPullbackHom Λ g) ▷ _ ≫ μ[(ProEtale.upperStar Ab.{u + 1} g).obj
      (condensedRingObj Λ X)]) ≫ condensedPullbackHom Λ g =
      _ ◁ condensedPullbackHom Λ g ≫ μ[condensedRingObj Λ Y]
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp])

omit [IsCommMonObj Λ] in
/-- The underlying morphism of `normalizedUpperStarRegularIso` is `α_g`. -/
lemma normalizedUpperStarRegularIso_hom_hom {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (normalizedUpperStarRegularIso Λ g).hom.hom = condensedPullbackHom Λ g := rfl

omit [IsCommMonObj Λ] in
/-- The underlying morphism of the inverse of `normalizedUpperStarRegularIso` is `α_g⁻¹`. -/
lemma normalizedUpperStarRegularIso_inv_hom {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (normalizedUpperStarRegularIso Λ g).inv.hom = inv (condensedPullbackHom Λ g) := rfl

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The pullback of the constant global section `p_X^* s` along `g`, followed by the coefficient
comparison `α_g`, is the constant global section `p_Y^* s`. -/
lemma ε_comp_map_constSection_comp_condensedPullbackHom {X Y : Scheme.{u}} (g : Y ⟶ X)
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    (Functor.LaxMonoidal.ε (ProEtale.upperStar Ab.{u + 1} g) ≫
      (ProEtale.upperStar Ab.{u + 1} g).map (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map s)) ≫ condensedPullbackHom Λ g =
      Functor.LaxMonoidal.ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s := by
  have h := NatTrans.IsMonoidal.ε_comp_map_comp_app (upperStarFromPointComp g).hom s
  have e : Functor.LaxMonoidal.ε (upperStarFromPoint X ⋙ ProEtale.upperStar Ab.{u + 1} g) =
    Functor.LaxMonoidal.ε (ProEtale.upperStar Ab.{u + 1} g) ≫
      (ProEtale.upperStar Ab.{u + 1} g).map (Functor.LaxMonoidal.ε (upperStarFromPoint X)) := rfl
  rw [e, Functor.comp_map, Category.assoc] at h
  rw [← h, Functor.map_comp, Category.assoc, Category.assoc]

/-- The normalized pullback of the multiplication by a constant global section is the
multiplication by the same constant global section. -/
lemma normalizedUpperStar_constRegularEnd {X Y : Scheme.{u}} (g : Y ⟶ X)
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    (normalizedUpperStarRegularIso Λ g).inv ≫
        (normalizedUpperStar Λ g).map (constRegularEnd Λ X s) ≫
          (normalizedUpperStarRegularIso Λ g).hom =
      constRegularEnd Λ Y s := by
  apply Mod.hom_ext
  have h : ((normalizedUpperStar Λ g).map (constRegularEnd Λ X s)).hom =
      (ProEtale.upperStar Ab.{u + 1} g).map (constRegularEnd Λ X s).hom := rfl
  rw [constRegularEnd_hom Λ Y, ← ε_comp_map_constSection_comp_condensedPullbackHom Λ g s,
    Mod.globalSmul_comp_regular_of_isIso, Mod.comp_hom', Mod.comp_hom',
    normalizedUpperStarRegularIso_hom_hom, normalizedUpperStarRegularIso_inv_hom, h,
    constRegularEnd_hom Λ X, ← Mod.globalSmul_mapMod, Mod.globalSmul_mapMod_regular]

/-- The pullback `g^*` of the regular module is the regular module. -/
noncomputable def upperStarRegularIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (g)^*⟦Λ⟧.obj (Mod.regular (condensedRingObj Λ X)) ≅ Mod.regular (condensedRingObj Λ Y) :=
  (upperStarIsoNormalizedUpperStar Λ g).app _ ≪≫ normalizedUpperStarRegularIso Λ g

/-- The pullback `g^*` of the multiplication by a constant global section is the multiplication
by the same constant global section. -/
lemma upperStar_constRegularEnd {X Y : Scheme.{u}} (g : Y ⟶ X)
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    (upperStarRegularIso Λ g).inv ≫ (g)^*⟦Λ⟧.map (constRegularEnd Λ X s) ≫
        (upperStarRegularIso Λ g).hom = constRegularEnd Λ Y s := by
  rw [← normalizedUpperStar_constRegularEnd Λ g s, upperStarRegularIso, Iso.trans_inv,
    Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    (upperStarIsoNormalizedUpperStar Λ g).hom.naturality_assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- The pullback `g^*` of the cokernel of the multiplication by a constant global section is the
cokernel of the multiplication by the same constant global section. -/
noncomputable def upperStarCokernelConstRegularEndIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    (g)^*⟦Λ⟧.obj (cokernel (constRegularEnd Λ X s)) ≅ cokernel (constRegularEnd Λ Y s) :=
  PreservesCokernel.iso (g)^*⟦Λ⟧ (constRegularEnd Λ X s) ≪≫
    cokernel.mapIso _ _ (upperStarRegularIso Λ g) (upperStarRegularIso Λ g) (by
      rw [← upperStar_constRegularEnd Λ g s, Iso.hom_inv_id_assoc])

/-- The constant module `⊕ⱼ Λ_X / sⱼ ⊕ Λ_X^r`, for global sections `s₁, …, s_k` of `Λ`. -/
noncomputable def constModule (X : Scheme.{u}) {k : ℕ}
    (s : Fin k → (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ)) (r : ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (⨁ fun j ↦ cokernel (constRegularEnd Λ X (s j))) ⊞ Mod.finiteFree _ r

/-- The pullback of a constant module is the constant module. -/
noncomputable def upperStarConstModuleIso {X Y : Scheme.{u}} (g : Y ⟶ X) {k : ℕ}
    (s : Fin k → (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ)) (r : ℕ) :
    (g)^*⟦Λ⟧.obj (constModule Λ X s r) ≅ constModule Λ Y s r :=
  (g)^*⟦Λ⟧.mapBiprod _ _ ≪≫
    biprod.mapIso ((g)^*⟦Λ⟧.mapBiproduct _ ≪≫
        biproduct.mapIso fun j ↦ upperStarCokernelConstRegularEndIso Λ g (s j))
      (Mod.finiteFreeIsoMap (g)^*⟦Λ⟧ (upperStarRegularIso Λ g) r)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Chart

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The multiplication by the constant global section `t` on the regular module `T̲` is the
multiplication by the constant `t`. -/
private lemma regularLift_continuousMapConstRingHom_hom (t : T) :
    (Mod.regularLift (Mod.regular (Profinite.continuousMapRingObj.{u} T))
      (Profinite.continuousMapConstRingHom T t).hom).hom =
      Profinite.continuousMapRingObjMulLeft T t := by
  rw [Mod.regularLift_regular_hom_eq_globalSmul]
  exact Profinite.globalSmul_continuousMapConstRingHom T t

/-- The continuous coefficient realization intertwines the multiplication by a constant `t` on
`p_X^* C(-, T)` with the multiplication by the constant function `t` on `C(-, T)_X`. -/
lemma map_continuousMapRingObjMulLeft_comp_chartComparison (X : Scheme.{u}) (t : T) :
    (upperStarFromPoint X).map
        (Profinite.continuousMapRingObjMulLeft T t) ≫
      chartComparison X T =
      chartComparison X T ≫ (continuousMultiplier X T (ContinuousMap.const X t)).hom := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [chartComparison, adj, Equiv.apply_symm_apply]
  ext S f
  exact ULift.ext (ContinuousMap.ext fun _ ↦ mul_comm _ _)

/-- In the continuous coefficient realization, the multiplication by the constant global section
`t` is the multiplication by the constant function `t`. -/
lemma regularIsoOfIsIso_conj_constRegularEnd (X : Scheme.{u}) [IsIso (chartComparison X T)]
    (t : T) :
    (Mod.regularIsoOfIsIso (chartComparison X T)).inv ≫
        (Mod.comap (inv (chartComparison X T))).map
          (constRegularEnd (Profinite.continuousMapRingObj T) X
            (Profinite.continuousMapConstRingHom.{u} T t).hom) ≫
        (Mod.regularIsoOfIsIso (chartComparison X T)).hom =
      continuousMultiplier X T (ContinuousMap.const X t) := by
  apply Mod.hom_ext
  have h : (constRegularEnd (Profinite.continuousMapRingObj T) X
      (Profinite.continuousMapConstRingHom.{u} T t).hom).hom =
      (upperStarFromPoint X).map
        (Profinite.continuousMapRingObjMulLeft T t) := by
    rw [constRegularEnd, Mod.regularLift_regular_obj_hom,
      regularLift_continuousMapConstRingHom_hom]
  rw [Mod.comp_hom', Mod.comp_hom']
  erw [h]
  exact (IsIso.inv_comp_eq _).2 (map_continuousMapRingObjMulLeft_comp_chartComparison T X t)

end Chart

end AlgebraicGeometry.ProEtale.CondensedRing


namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Two regular-module endomorphisms over continuous coefficients commute. -/
lemma continuousRegular_comm (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (g h : Mod.regular (continuousAbRing X O) ⟶ Mod.regular (continuousAbRing X O)) :
    g ≫ h = h ≫ g := by
  apply regularCoefficient_injective X O
  rw [regularCoefficient_comp, regularCoefficient_comp, mul_comm]

/-- A matrix entry of constant norm `‖ϖ‖ ^ e` dominating all entries of an integral matrix
divides its row and its column, is rationally invertible, and is a unit multiple of the constant
`ϖ ^ e`. -/
theorem integralMatrix_pivot_data (X : Scheme.{u}) {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) (ϖ : continuousIntegers ℓ E) (hϖ : (ϖ : E) ≠ 0) (e : ℕ)
    (hnorm : ∀ x, ‖(integralMatrixFunctions ℓ E X
      (chartComparison X (continuousIntegers ℓ E)) f i j x : E)‖ = ‖(ϖ : E)‖ ^ e)
    (hbound : ∀ r s x, ‖(integralMatrixFunctions ℓ E X
      (chartComparison X (continuousIntegers ℓ E)) f r s x : E)‖ ≤
      ‖(integralMatrixFunctions ℓ E X
        (chartComparison X (continuousIntegers ℓ E)) f i j x : E)‖) :
    let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
    (∃ q : Fin n → (Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
        Mod.regular (condensedRingObj (integralCoeff ℓ E) X)),
      ∀ k, q k ≫ p = biproduct.ι _ k ≫ f ≫ biproduct.π _ i) ∧
    (∃ q' : Fin t → (Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
        Mod.regular (condensedRingObj (integralCoeff ℓ E) X)),
      ∀ k, p ≫ q' k = biproduct.ι _ j ≫ f ≫ biproduct.π _ k) ∧
    IsIso ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map p) ∧
    ∃ v : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ≅
        Mod.regular (condensedRingObj (integralCoeff ℓ E) X),
      p = v.hom ≫ constRegularEnd (integralCoeff ℓ E) X
        (Profinite.continuousMapConstRingHom.{u} (continuousIntegers ℓ E) (ϖ ^ e)).hom := by
  intro p
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let O := continuousIntegers ℓ E
  let R := condensedRingObj (integralCoeff ℓ E) X
  let ec := chartComparison X O
  let eE := chartComparison X E
  have : IsIso eE := chartComparison_isIso X E
  have hcompat : coefficientMap (integralScalarMap ℓ E) X ≫ eE =
      ec ≫ integralFunctionInclusion ℓ E X :=
    chartComparison_naturality X O E O.subtype continuous_subtype_val
  have hpow : ‖(ϖ : E)‖ ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hϖ)
  have hzero (x : X) : (integralMatrixFunctions ℓ E X ec f i j x : E) ≠ 0 := by
    intro h
    apply hpow
    rw [← hnorm x, h, norm_zero]
  obtain ⟨-, hunit, q, hq⟩ :=
    integralMatrix_entry_properties ℓ E X ec eE hcompat f i j hzero hbound
  refine ⟨⟨q, hq⟩, ?_, hunit, ?_⟩
  · let K := (Mod.comapEquivalenceOfIsIso (inv ec)).functor
    have : K.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv ec)).isEquivalence_functor
    let jR := Mod.regularIsoOfIsIso ec
    let p' := jR.inv ≫ K.map p ≫ jR.hom
    let g (k : Fin t) := biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ Mod.regular R) k
    let g' (k : Fin t) := jR.inv ≫ K.map (g k) ≫ jR.hom
    have hdiv (k : Fin t) : ∃ q, q ≫ p' = g' k :=
      continuousIntegral_divides ℓ E X p' (g' k) hzero (fun x ↦ hbound k j x)
    choose q' hq' using hdiv
    refine ⟨fun k ↦ K.preimage (jR.hom ≫ q' k ≫ jR.inv), fun k ↦ ?_⟩
    apply K.map_injective
    rw [K.map_comp, Functor.map_preimage]
    have h := congrArg (fun z ↦ jR.hom ≫ z ≫ jR.inv)
      ((continuousRegular_comm X O p' (q' k)).trans (hq' k))
    simpa only [p', g', Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  · let K := (Mod.comapEquivalenceOfIsIso (inv ec)).functor
    have : K.IsEquivalence := (Mod.comapEquivalenceOfIsIso (inv ec)).isEquivalence_functor
    let jR := Mod.regularIsoOfIsIso ec
    let p' := jR.inv ≫ K.map p ≫ jR.hom
    have hp' (x : X) : (regularCoefficient X O p' x : E) =
        integralMatrixFunctions ℓ E X ec f i j x := rfl
    have hϖe : ((ϖ ^ e : O) : E) ≠ 0 := by
      rw [SubmonoidClass.coe_pow]
      exact pow_ne_zero _ hϖ
    have hnorm' (x : X) : ‖(regularCoefficient X O p' x : E)‖ = ‖((ϖ ^ e : O) : E)‖ := by
      rw [hp', hnorm, SubmonoidClass.coe_pow, norm_pow]
    have hmem (a b : O) (h : ‖(a : E)‖ = ‖(b : E)‖) (hb : (b : E) ≠ 0) :
        (a : E) / b ∈ O := by
      change ‖(a : E) / b‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, norm_div, h,
        div_self (norm_ne_zero_iff.mpr hb)]
    have hp'0 (x : X) : (regularCoefficient X O p' x : E) ≠ 0 := by
      rw [hp']
      exact hzero x
    let u : C(X, O) := ⟨fun x ↦ ⟨_, hmem _ _ (hnorm' x) hϖe⟩,
      ((continuous_subtype_val.comp (regularCoefficient X O p').continuous).div_const
        _).subtype_mk _⟩
    let u' : C(X, O) := ⟨fun x ↦ ⟨_, hmem _ _ (hnorm' x).symm (hp'0 x)⟩,
      (continuous_const.div (continuous_subtype_val.comp (regularCoefficient X O p').continuous)
        hp'0).subtype_mk _⟩
    have huu' : u * u' = 1 := by
      refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
      simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, MulMemClass.coe_mul,
        OneMemClass.coe_one, u, u', ContinuousMap.coe_mk]
      rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero hϖe (hp'0 x))]
    let V' : Mod.regular (continuousAbRing X O) ≅ Mod.regular (continuousAbRing X O) :=
      { hom := continuousMultiplier X O u
        inv := continuousMultiplier X O u'
        hom_inv_id := by
          apply regularCoefficient_injective X O
          rw [regularCoefficient_comp, regularCoefficient_multiplier,
            regularCoefficient_multiplier, regularCoefficient_id, huu']
        inv_hom_id := by
          apply regularCoefficient_injective X O
          rw [regularCoefficient_comp, regularCoefficient_multiplier,
            regularCoefficient_multiplier, regularCoefficient_id, mul_comm, huu'] }
    refine ⟨K.preimageIso (jR ≪≫ V' ≪≫ jR.symm), ?_⟩
    have hc := regularIsoOfIsIso_conj_constRegularEnd O X (ϖ ^ e)
    have key : p' = V'.hom ≫ continuousMultiplier X O (ContinuousMap.const X (ϖ ^ e)) := by
      apply regularCoefficient_injective X O
      rw [regularCoefficient_comp, regularCoefficient_multiplier, regularCoefficient_multiplier]
      refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
      simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, MulMemClass.coe_mul, u,
        ContinuousMap.coe_mk]
      rw [div_mul_cancel₀ _ hϖe]
    rw [← hc] at key
    apply K.map_injective
    calc K.map p = jR.hom ≫ p' ≫ jR.inv := by simp [p']
      _ = K.map ((K.preimageIso (jR ≪≫ V' ≪≫ jR.symm)).hom ≫
          constRegularEnd (integralCoeff ℓ E) X
            (Profinite.continuousMapConstRingHom.{u} O (ϖ ^ e)).hom) := by
        rw [key, Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
        simp
        rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- If every nonzero element of `𝒪_E` has norm a power of `‖ϖ‖`, then after refining a cover on
which the rational cokernel is free, a map between standard finite free modules is either zero or
has an entry of constant norm `‖ϖ‖ ^ e` dominating all entries. -/
theorem integralMatrix_analytic_cover_pow (ϖ : continuousIntegers ℓ E)
    (hval : ∀ z : continuousIntegers ℓ E, z ≠ 0 → ∃ e : ℕ, ‖(z : E)‖ = ‖(ϖ : E)‖ ^ e)
    (n t₀ : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t₀)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      let f := (integralFiniteFreePullbackIso ℓ E (V.f k) n).inv ≫ T.map a ≫
        (integralFiniteFreePullbackIso ℓ E (V.f k) t₀).hom
      T.map a = 0 ∨ ∃ (i : Fin t₀) (j : Fin n) (e : ℕ),
        (∀ x, ‖(integralMatrixFunctions ℓ E (V.X k)
          (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x : E)‖ =
            ‖(ϖ : E)‖ ^ e) ∧
        ∀ r s x,
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f r s x : E)‖ ≤
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x : E)‖ := by
  classical
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  obtain ⟨V, hV⟩ := integralMatrix_zero_neighborhood ℓ E n t₀ X a hC
  have hlocal (k : V.I₀) (x : V.X k) :
      ∃ U : (V.X k).Opens, x ∈ U ∧
        ((integralMatrixPullback ℓ E (U.ι ≫ V.f k)).map a = 0 ∨
          ∃ (i : Fin t₀) (j : Fin n) (e : ℕ),
            (∀ y : U.toScheme,
              ‖(integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a i j y : E)‖ =
                ‖(ϖ : E)‖ ^ e) ∧
            ∀ r s (y : U.toScheme),
              ‖(integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a r s y : E)‖ ≤
              ‖(integralMatrixPullbackFunctions ℓ E (U.ι ≫ V.f k) a i j y : E)‖) := by
    by_cases hz : ∀ i j, integralMatrixPullbackFunctions ℓ E (V.f k) a i j x = 0
    · obtain ⟨U, hxU, hU⟩ := hV k x hz
      exact ⟨U, hxU, Or.inl hU⟩
    · push Not at hz
      obtain ⟨i, j, hij⟩ := hz
      let b : Fin t₀ × Fin n → C(V.X k, E) := fun p ↦
        ⟨fun y ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a p.1 p.2 y).val,
          continuous_subtype_val.comp
            (integralMatrixPullbackFunctions ℓ E (V.f k) a p.1 p.2).continuous⟩
      have hb : ∃ p, b p x ≠ 0 :=
        ⟨(i, j), fun h ↦ hij (Subtype.ext h)⟩
      obtain ⟨W, p, hW, hxW, hp, hbound⟩ :=
        ContinuousMap.exists_open_dominating_member b x hb
      obtain ⟨e, he⟩ := hval (integralMatrixPullbackFunctions ℓ E (V.f k) a p.1 p.2 x)
        (fun h ↦ hp x hxW (congrArg Subtype.val h))
      let W' : Set (V.X k) := W ∩ {y | ‖b p y - b p x‖ < ‖b p x‖}
      have hW' : IsOpen W' := hW.inter
        (isOpen_lt ((b p).continuous.sub continuous_const).norm continuous_const)
      have hxW' : x ∈ W' := ⟨hxW, by
        simpa only [Set.mem_ofPred_eq, sub_self, norm_zero] using
          norm_pos_iff.mpr (hp x hxW)⟩
      have hconst (y : V.X k) (hy : y ∈ W') : ‖b p y‖ = ‖b p x‖ := by
        have h : ‖b p y + -(b p x)‖ < max ‖b p y‖ ‖-(b p x)‖ := by
          simpa only [norm_neg, ← sub_eq_add_neg] using
            hy.2.trans_le (le_max_right ‖b p y‖ ‖b p x‖)
        simpa only [norm_neg] using IsUltrametricDist.norm_eq_of_add_norm_lt_max h
      let U : (V.X k).Opens := ⟨W', hW'⟩
      refine ⟨U, hxW', Or.inr ⟨p.1, p.2, e, ?_, ?_⟩⟩
      · intro y
        rw [integralMatrixFunctions_pullback]
        exact (hconst y.val y.property).trans he
      · intro r s y
        rw [integralMatrixFunctions_pullback, integralMatrixFunctions_pullback]
        exact hbound (r, s) y.val y.property.1
  have hcover := cover_of_open_neighborhoods V
    (fun Y g ↦ (integralMatrixPullback ℓ E g).map a = 0 ∨
      ∃ (i : Fin t₀) (j : Fin n) (e : ℕ),
        (∀ y, ‖(integralMatrixPullbackFunctions ℓ E g a i j y : E)‖ = ‖(ϖ : E)‖ ^ e) ∧
        ∀ r s y, ‖(integralMatrixPullbackFunctions ℓ E g a r s y : E)‖ ≤
          ‖(integralMatrixPullbackFunctions ℓ E g a i j y : E)‖) hlocal
  simpa only [integralMatrixPullbackFunctions, integralMatrixPullbackMap,
    integralMatrixPullback] using hcover

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- One integral pivot of norm `‖ϖ‖ ^ e`, after refining a free rational cokernel cover: locally,
a map from a finite free module to a free module is either zero or has cokernel
`𝒪/ϖ^e ⊕ coker s` for a smaller map `s` whose rational cokernel is again locally free. -/
theorem integralMatrix_pivot_cover_pow (ϖ : continuousIntegers ℓ E)
    (hval : ∀ z : continuousIntegers ℓ E, z ≠ 0 → ∃ e : ℕ, ‖(z : E)‖ = ‖(ϖ : E)‖ ^ e)
    (hϖ : (ϖ : E) ≠ 0)
    (n : ℕ) (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B)
    (hA : Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n))
    (hB : Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      T.map a = 0 ∨
        ∃ (m : ℕ), m < n ∧
          ∃ (A₁ B₁ : Mod (Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) R)
            (_ : A₁ ≅ Mod.finiteFree R m),
            Mod.IsFree R B₁ ∧ ∃ (e : ℕ) (s : A₁ ⟶ B₁),
              Nonempty (cokernel (T.map a) ≅
                cokernel (constRegularEnd (integralCoeff ℓ E) (V.X k)
                  (Profinite.continuousMapConstRingHom.{u} (continuousIntegers ℓ E)
                    (ϖ ^ e)).hom) ⊞ cokernel s) ∧
              ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage (V.X k), ∀ l,
                Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (W.f l)).obj
                    (condensedRingObj (Profinite.continuousMapRingObj E) (V.X k)))
                  (((ProEtale.upperStar Ab.{u + 1} (W.f l)).mapMod _).obj
                    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (V.X k))).obj
                      (cokernel s))) := by
  classical
  obtain ⟨eA₀⟩ := hA
  obtain ⟨t₀, ⟨eB₀⟩⟩ := hB
  let R₀ := condensedRingObj (integralCoeff ℓ E) X
  let f₀ : Mod.finiteFree R₀ n ⟶ Mod.finiteFree R₀ t₀ := eA₀.inv ≫ a ≫ eB₀.hom
  let ec : cokernel a ≅ cokernel f₀ := cokernel.mapIso a f₀ eA₀ eB₀ (by simp [f₀])
  have hC₀ : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel f₀))) := by
    obtain ⟨U, hU⟩ := hC
    refine ⟨U, fun k ↦ ?_⟩
    obtain ⟨q, ⟨eq⟩⟩ := hU k
    let G := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)
    let F := (ProEtale.upperStar Ab.{u + 1} (U.f k)).mapMod
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
    exact ⟨q, ⟨(F.mapIso (G.mapIso ec)).symm ≪≫ eq⟩⟩
  obtain ⟨V, hV⟩ := integralMatrix_analytic_cover_pow ℓ E ϖ hval n t₀ X f₀ hC₀
  refine ⟨V, fun k ↦ ?_⟩
  intro R T
  rcases hV k with hz | ⟨i, j, e, hnorm, hbound⟩
  · left
    have ha₀ : a = eA₀.hom ≫ f₀ ≫ eB₀.inv := by simp [f₀]
    rw [ha₀, Functor.map_comp, Functor.map_comp, hz, Limits.zero_comp, Limits.comp_zero]
  · right
    let eA₁ := integralFiniteFreePullbackIso ℓ E (V.f k) n
    let eB₁ := integralFiniteFreePullbackIso ℓ E (V.f k) t₀
    let eA := T.mapIso eA₀ ≪≫ eA₁
    let eB := T.mapIso eB₀ ≪≫ eB₁
    let f : Mod.finiteFree R n ⟶ Mod.finiteFree R t₀ := eA.inv ≫ T.map a ≫ eB.hom
    have hf : f = eA₁.inv ≫ T.map f₀ ≫ eB₁.hom := by
      simp only [f, eA, eB, f₀, Iso.trans_inv, Iso.trans_hom,
        Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    obtain ⟨⟨q, hq⟩, ⟨q', hq'⟩, hunit, v, hv⟩ :=
      integralMatrix_pivot_data ℓ E (V.X k) f i j ϖ hϖ e
        (by simpa only [hf] using hnorm) (by simpa only [hf] using hbound)
    let p := biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : Fin t₀ ↦ Mod.regular R) i
    obtain ⟨m, s, hmn, eA', eB', r, c, d, hblock⟩ :=
      finiteBiproduct_pivot_block f i j p rfl q hq q' hq'
    let b := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc (p ≫ c) d)
    let eAA := eA ≪≫ eA'
    let eBB := eB ≪≫ eB'
    have hsq : eAA.inv ≫ T.map a ≫ eBB.hom = b := by
      simpa only [eAA, eBB, f, Iso.trans_inv, Iso.trans_hom, Category.assoc] using hblock
    let eC : cokernel (T.map a) ≅ cokernel b :=
      cokernel.mapIso (T.map a) b eAA eBB (conjugate_eq eAA eBB (T.map a) b hsq).symm
    have hLF := rationalCokernelFree_pullback ℓ E (V.f k) a hC
    let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (V.X k))
    have : IsIso (L.map p) := hunit
    refine ⟨m, hmn, Mod.finiteFree R m, Mod.finiteFree R s, Iso.refl _, ⟨s, ⟨Iso.refl _⟩⟩, e,
      d - r ≫ p ≫ c, ⟨eC ≪≫ cokernelBiprodBlockIso p r c d ≪≫
        biprod.mapIso (cokernelIsoOfEq hv ≪≫ cokernelEpiComp _ _) (Iso.refl _)⟩,
      locally_free_of_iso hLF (L.mapIso eC ≪≫ mappedPivotCokernelIso L p r (p ≫ c) d)⟩

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  preservesBinaryBiproducts_of_preservesBiproducts

section Bind

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A property of the members of the covers `W k` of the members of `V`, phrased through their
composite structure morphisms, holds for the members of the refined cover `V.bind W`. -/
lemma forall_cover_bind {X : Scheme.{u}} (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (V : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (W : ∀ k, Scheme.Cover.{u} Scheme.proetalePrecoverage (V.X k))
    (h : ∀ k l, Q ((W k).X l) ((W k).f l ≫ V.f k)) :
    ∀ i, Q ((V.bind W).X i) ((V.bind W).f i) := by
  rintro ⟨k, l⟩
  exact h k l

/-- A property of module objects which holds pro-étale locally on the members of a pro-étale
cover holds on the members of a refined pro-étale cover. -/
lemma exists_cover_of_forall_exists_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : ∀ Y : Scheme.{u}, Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y) → Prop)
    (hP : ∀ (Y : Scheme.{u}) (N N' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)), Nonempty (N ≅ N') → P Y N → P Y N')
    (V : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ k, ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage (V.X k), ∀ l,
      P (W.X l) ((W.f l)^*⟦Λ⟧.obj ((V.f k)^*⟦Λ⟧.obj M))) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i, P (U.X i) ((U.f i)^*⟦Λ⟧.obj M) := by
  obtain ⟨W, hW⟩ := Classical.axiomOfChoice h
  exact ⟨V.bind W, forall_cover_bind (fun Y g ↦ P Y ((g)^*⟦Λ⟧.obj M)) V W
    fun k l ↦ hP _ _ _ ⟨(((upperStarComp Λ ((W k).f l) (V.f k)).app M) ≪≫
      eqToIso (Functor.comp_obj _ _ _)).symm⟩ (hW k l)⟩

/-- A property of a module object holds on the members of the trivial pro-étale cover. -/
lemma exists_cover_of_prop {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : ∀ Y : Scheme.{u}, Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y) → Prop)
    (hP : ∀ (Y : Scheme.{u}) (N N' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)), Nonempty (N ≅ N') → P Y N → P Y N')
    (h : P X M) :
    ∃ W : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ l, P (W.X l) ((W.f l)^*⟦Λ⟧.obj M) :=
  ⟨.singleton (𝟙 X) (Scheme.proetalePrecoverage.mem_coverings_of_isIso _),
    fun _ ↦ hP _ _ _ ⟨((upperStarId Λ X).app M ≪≫ eqToIso (Functor.id_obj _)).symm⟩ h⟩

end Bind

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The pullback of a module object whose scalar extension to `E_X` is pro-étale locally free has
the same property. -/
lemma rationalLocallyFree_normalizedUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (integralCoeff ℓ E) X)}
    (hN : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) Y))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj
            ((normalizedUpperStar (integralCoeff ℓ E) g).obj N))) := by
  let F := ProEtale.upperStar Ab.{u + 1} g
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let ψ := coefficientMap (integralScalarMap ℓ E) Y
  let e := condensedPullbackHom (integralCoeff ℓ E) g
  let d := condensedPullbackHom (Profinite.continuousMapRingObj E) g
  let K := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv d)
  have hsq : e ≫ ψ = F.map φ ≫ d :=
    (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) g).symm
  let i : (Mod.extendScalars ψ).obj ((normalizedUpperStar (integralCoeff ℓ E) g).obj N) ≅
      K.obj ((F.mapMod S).obj ((Mod.extendScalars φ).obj N)) :=
    (extendScalarsComapSquareIso (F.map φ) ψ e d hsq).app ((F.mapMod R).obj N) ≪≫
      K.mapIso ((pullbackExtendScalarsComparison g R S φ).symm.app N)
  exact locally_free_of_iso (locally_free_comap (inv d) (locally_free_pullback g hN)) i.symm


/-- On a scheme with noetherian underlying space, the scalar extension to `E_X` of a pro-étale
locally finitely presented `𝒪_{E,X}`-module is pro-étale locally free. -/
lemma rationalLocallyFree_of_isLocallyFinitelyPresented [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (integralCoeff ℓ E) X)}
    (hP : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) P) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj P)) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let P_E := (Mod.extendScalars φ).obj P
  have hPE : IsLocallyFinitelyPresented S P_E := lfp_extend R S φ hP
  let ψ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  have : IsMonHom ψ.hom := Sheaf.isMonHom_sheafCompose_map _ (liftCoefficientIso E).hom
  let ψX := (upperStarFromPoint X).map ψ.hom
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro T a b
        apply ULift.ext
        change (a.down * b.down : C(T.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv ψX)).obj P_E) (lfp_comap (inv ψX) hPE)
  exact locally_free_of_iso (locally_free_comap ψX h)
    ((Mod.comapEquivalenceOfIsIso ψX).counitIso.app P_E)


/-- The constant module `⊕ⱼ 𝒪_X/ϖ^{eⱼ} ⊕ 𝒪_X^r` over the integral coefficient ring. -/
noncomputable abbrev integralConstModule (X : Scheme.{u}) (ϖ : continuousIntegers ℓ E)
    (k r : ℕ) (e : Fin k → ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (integralCoeff ℓ E) X) :=
  constModule (integralCoeff ℓ E) X
    (fun j ↦ (Profinite.continuousMapConstRingHom.{u} (continuousIntegers ℓ E) (ϖ ^ e j)).hom) r

/-- A module object over `𝒪_{E,Y}` is isomorphic to a constant module `⊕ⱼ 𝒪_Y/ϖ^{eⱼ} ⊕ 𝒪_Y^r`. -/
def IsIntegralConstModule (ϖ : continuousIntegers ℓ E) (Y : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) : Prop :=
  ∃ (K r : ℕ) (e : Fin K → ℕ), Nonempty (N ≅ integralConstModule ℓ E Y ϖ K r e)

/-- Being isomorphic to a constant module is invariant under isomorphism. -/
lemma IsIntegralConstModule.of_iso {ϖ : continuousIntegers ℓ E} {Y : Scheme.{u}}
    {N N' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)} (hN : Nonempty (N ≅ N'))
    (h : IsIntegralConstModule ℓ E ϖ Y N) : IsIntegralConstModule ℓ E ϖ Y N' := by
  obtain ⟨i⟩ := hN
  obtain ⟨K, r, e, ⟨j⟩⟩ := h
  exact ⟨K, r, e, ⟨i.symm ≪≫ j⟩⟩

/-- **Smith normal form, pro-étale locally**: if every nonzero element of `𝒪_E` has norm a power
of `‖ϖ‖`, the cokernel of a map from a finite free to a free `𝒪_{E,X}`-module whose rational
cokernel is pro-étale locally free is, pro-étale locally, a constant module. -/
theorem exists_cover_isIntegralConstModule_of_presentation (ϖ : continuousIntegers ℓ E)
    (hval : ∀ z : continuousIntegers ℓ E, z ≠ 0 → ∃ e : ℕ, ‖(z : E)‖ = ‖(ϖ : E)‖ ^ e)
    (hϖ : (ϖ : E) ≠ 0) (n : ℕ) :
    ∀ (X : Scheme.{u}) (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
    Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
    (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) →
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      IsIntegralConstModule ℓ E ϖ (V.X k) ((V.f k)^*⟦integralCoeff ℓ E⟧.obj (cokernel a)) := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro X A B a hA hB hC
    obtain ⟨V, hV⟩ := integralMatrix_pivot_cover_pow ℓ E ϖ hval hϖ n X A B a hA hB hC
    refine exists_cover_of_forall_exists_cover (integralCoeff ℓ E) (cokernel a)
      (IsIntegralConstModule ℓ E ϖ) (fun _ _ _ ↦ IsIntegralConstModule.of_iso ℓ E) V
      fun k ↦ ?_
    let T := normalizedUpperStar (integralCoeff ℓ E) (V.f k)
    let ν : (V.f k)^*⟦integralCoeff ℓ E⟧.obj (cokernel a) ≅ cokernel (T.map a) :=
      (upperStarIsoNormalizedUpperStar (integralCoeff ℓ E) (V.f k)).app (cokernel a) ≪≫
        PreservesCokernel.iso T a
    rcases hV k with hz | ⟨m, hmn, A₁, B₁, iA, hB₁, e, s, ⟨i₁⟩, hs⟩
    · obtain ⟨t, ⟨eB⟩⟩ := hB
      exact exists_cover_of_prop (integralCoeff ℓ E) _ (IsIntegralConstModule ℓ E ϖ)
        (fun _ _ _ ↦ IsIntegralConstModule.of_iso ℓ E) ⟨0, t, Fin.elim0, ⟨ν ≪≫
          cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget ≪≫ T.mapIso eB ≪≫
          integralFiniteFreePullbackIso ℓ E (V.f k) t ≪≫
          isoZeroBiprod (isZero_biproduct_fin_zero _)⟩⟩
    · obtain ⟨W, hW⟩ := IH m hmn (V.X k) A₁ B₁ s ⟨iA⟩ hB₁ hs
      refine ⟨W, fun l ↦ ?_⟩
      obtain ⟨K, r, e', ⟨i₂⟩⟩ := hW l
      let G := (W.f l)^*⟦integralCoeff ℓ E⟧
      exact ⟨K + 1, r, Fin.cons e e', ⟨G.mapIso (ν ≪≫ i₁) ≪≫ G.mapBiprod _ _ ≪≫
        biprod.mapIso (upperStarCokernelConstRegularEndIso (integralCoeff ℓ E) (W.f l) _) i₂ ≪≫
        biprodBiproductConsIso (fun x ↦ cokernel (constRegularEnd (integralCoeff ℓ E) (W.X l)
          (Profinite.continuousMapConstRingHom.{u} (continuousIntegers ℓ E) (ϖ ^ x)).hom)) e e'
          _⟩⟩


/-- **Lisse `𝒪_E`-sheaves are locally constant**, for the integral coefficient ring of a normed
finite extension `E` of `ℚ_ℓ` in which every nonzero integer has norm a power of `‖ϖ‖`. -/
theorem exists_cover_isIntegralConstModule [FiniteDimensional ℚ_[ℓ] E] (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj (integralCoeff ℓ E) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) Z) M)
    (ϖ : continuousIntegers ℓ E)
    (hval : ∀ z : continuousIntegers ℓ E, z ≠ 0 → ∃ e : ℕ, ‖(z : E)‖ = ‖(ϖ : E)‖ ^ e)
    (hϖ : (ϖ : E) ≠ 0) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z, ∀ i,
      IsIntegralConstModule ℓ E ϖ (𝒰.X i) ((𝒰.f i)^*⟦integralCoeff ℓ E⟧.obj M) := by
  have hR := rationalLocallyFree_of_isLocallyFinitelyPresented ℓ E Z hM
  obtain ⟨U, hU⟩ := hM
  refine exists_cover_of_forall_exists_cover (integralCoeff ℓ E) M
    (IsIntegralConstModule ℓ E ϖ) (fun _ _ _ ↦ IsIntegralConstModule.of_iso ℓ E) U
    fun i ↦ ?_
  let α := condensedPullbackHom (integralCoeff ℓ E) (U.f i)
  obtain ⟨n, m, a, ⟨eM⟩⟩ := fp_comap (inv α) (hU i)
  let ν : (U.f i)^*⟦integralCoeff ℓ E⟧.obj M ≅ cokernel a :=
    (upperStarIsoNormalizedUpperStar (integralCoeff ℓ E) (U.f i)).app M ≪≫ eM
  have hT := rationalLocallyFree_normalizedUpperStar ℓ E (U.f i) hR
  obtain ⟨W, hW⟩ := exists_cover_isIntegralConstModule_of_presentation ℓ E ϖ hval hϖ m
    (U.X i) _ _ a ⟨Iso.refl _⟩ ⟨n, ⟨Iso.refl _⟩⟩
    (locally_free_of_iso hT ((Mod.extendScalars _).mapIso eM))
  exact ⟨W, fun l ↦ IsIntegralConstModule.of_iso ℓ E ⟨((W.f l)^*⟦integralCoeff ℓ E⟧.mapIso
    ν).symm⟩ (hW l)⟩


section Transport

/-- Every pro-étale locally finitely presented `Λ_Z`-module on a scheme `Z` with noetherian
underlying space is, on the members of some pro-étale cover, isomorphic to a constant module
`⊕ⱼ Λ/σ(eⱼ) ⊕ Λ^r`. -/
def LfpLocallyConstModule (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (σ : ℕ → (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ)) :
    Prop :=
  ∀ (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
    IsLocallyFinitelyPresented (condensedRingObj Λ Z) M →
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z, ∀ i, ∃ (k r : ℕ) (e : Fin k → ℕ),
      Nonempty ((𝒰.f i)^*⟦Λ⟧.obj M ≅ constModule Λ (𝒰.X i) (fun j ↦ σ (e j)) r)

/-- `LfpLocallyConstModule` only depends on the ring object with its multiplication and on the
sections. -/
lemma LfpLocallyConstModule.of_eq {Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [i₁ : MonObj Λ₁] [IsCommMonObj Λ₁] [i₂ : MonObj Λ₂] [IsCommMonObj Λ₂]
    {σ₁ : ℕ → (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ₁)}
    {σ₂ : ℕ → (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ₂)}
    (hΛ : Λ₁ = Λ₂) (hi : HEq i₁ i₂) (hσ : HEq σ₁ σ₂) (h : LfpLocallyConstModule Λ₁ σ₁) :
    LfpLocallyConstModule Λ₂ σ₂ := by
  subst hΛ
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hσ
  exact h

end Transport

/-- **Lisse `𝒪_E`-sheaves are locally constant**, for the integral coefficient ring of a normed
finite extension `E` of `ℚ_ℓ` in which every nonzero integer has norm a power of `‖ϖ‖`. -/
theorem lfpLocallyConstModule_integralCoeff [FiniteDimensional ℚ_[ℓ] E]
    (ϖ : continuousIntegers ℓ E)
    (hval : ∀ z : continuousIntegers ℓ E, z ≠ 0 → ∃ e : ℕ, ‖(z : E)‖ = ‖(ϖ : E)‖ ^ e)
    (hϖ : (ϖ : E) ≠ 0) :
    LfpLocallyConstModule (integralCoeff ℓ E)
      (fun n ↦ (Profinite.continuousMapConstRingHom.{u} (continuousIntegers ℓ E) (ϖ ^ n)).hom) :=
  fun Z _ _ hM ↦ exists_cover_isIntegralConstModule ℓ E Z hM ϖ hval hϖ

end AlgebraicGeometry.ProEtale.CondensedRing

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- If the maximal ideal of `𝒪_E` is generated by `ϖ`, every nonzero element of `𝒪_E` has norm a
power of the norm of `ϖ`. -/
lemma exists_norm_eq_pow_of_maximalIdeal_eq_span (ϖ : integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    (z : integers ℓ E) (hz : z ≠ 0) :
    ∃ e : ℕ, ‖algebraMap E (PadicAlgCl ℓ) z‖ = ‖algebraMap E (PadicAlgCl ℓ) ϖ‖ ^ e := by
  let N : integers ℓ E → ℝ := fun x ↦ ‖algebraMap E (PadicAlgCl ℓ) x‖
  have hN_mul (x y : integers ℓ E) : N (x * y) = N x * N y := by
    simp only [N, MulMemClass.coe_mul, map_mul, norm_mul]
  have hN_le (x : integers ℓ E) : N x ≤ 1 := by
    have h := (mem_integers_iff ℓ E (x : E)).mp x.2
    rwa [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  have hN_pos (x : integers ℓ E) (hx : x ≠ 0) : 0 < N x := by
    refine norm_pos_iff.mpr fun h ↦ hx ?_
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap E (PadicAlgCl ℓ)).injective).mp h)
  have hN_unit (x : integers ℓ E) (hx : IsUnit x) : N x = 1 := by
    obtain ⟨v, rfl⟩ := hx
    have h := hN_mul v ↑v⁻¹
    rw [Units.mul_inv] at h
    have h1 : N 1 = 1 := by simp [N]
    rw [h1] at h
    nlinarith [hN_le v, hN_le ((v⁻¹ : (integers ℓ E)ˣ) : integers ℓ E),
      hN_pos v (Units.ne_zero v)]
  have hϖ0 : ϖ ≠ 0 := fun h ↦ maximalIdeal_integers_ne_bot ℓ E (by
    rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (integers ℓ E) := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hNϖ : N ϖ < 1 := by
    refine lt_of_le_of_ne (hN_le ϖ) fun h ↦ (IsLocalRing.mem_maximalIdeal _).mp hϖm ?_
    have hmem : ((ϖ : E))⁻¹ ∈ integers ℓ E := by
      rw [mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, map_inv₀,
        norm_inv]
      exact inv_le_one_of_one_le₀ h.ge
    have hne : (ϖ : E) ≠ 0 := fun h' ↦ hϖ0 (Subtype.ext h')
    exact IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hne))
  have key (n : ℕ) : ∀ x : integers ℓ E, x ≠ 0 → N ϖ ^ n < N x → ∃ e : ℕ, N x = N ϖ ^ e := by
    induction n with
    | zero =>
      intro x _ hx
      exact absurd (hN_le x) (by rw [pow_zero] at hx; exact not_le.mpr hx)
    | succ n ih =>
      intro x hx hlt
      by_cases hu : IsUnit x
      · exact ⟨0, by rw [hN_unit x hu, pow_zero]⟩
      · have hxm : x ∈ IsLocalRing.maximalIdeal (integers ℓ E) :=
          (IsLocalRing.mem_maximalIdeal _).mpr hu
        rw [hϖ] at hxm
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hxm
        have hy : y ≠ 0 := fun h ↦ hx (by rw [h, zero_mul])
        rw [hN_mul, pow_succ] at hlt
        obtain ⟨e, he⟩ := ih y hy (lt_of_mul_lt_mul_right hlt (hN_pos ϖ hϖ0).le)
        exact ⟨e + 1, by rw [hN_mul, he, pow_succ]⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hN_pos z hz) hNϖ
  exact key n z hz hn

end PadicAlgCl
