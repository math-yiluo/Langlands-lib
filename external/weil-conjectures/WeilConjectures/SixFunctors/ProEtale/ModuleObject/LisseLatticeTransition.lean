/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsFreeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# Transition matrices of trivialisations of module objects

Let `Λ` be a commutative condensed ring, `S` a scheme and `L` a module object over `Λ_S`. For a
trivialisation `e : Λ_Vⁿ ≅ f^* L` over `f : V ⟶ S` and a morphism `a : W ⟶ V`, the pullback of
`e` along `a` is a trivialisation `Λ_Wⁿ ≅ (a ≫ f)^* L`. For two trivialisations `e`, `e'` over
`f`, `f'` and `a : W ⟶ V`, `b : W ⟶ V'` with `a ≫ f = b ≫ f'`, the two trivialisations of
`(a ≫ f)^* L = (b ≫ f')^* L` differ by the *transition morphism* `Λ_Wⁿ ⟶ Λ_Wⁿ'`. Transition
morphisms

* are the identity for `e = e'`, `a = b` (`frameTransition_self`) and compose
  (`frameTransition_trans`);
* are compatible with precomposition by `c : Q ⟶ W` (`frameTransition_comp`): the transition
  morphism at `c ≫ a, c ≫ b` is the pullback of that at `a, b`;
* compute the transition isomorphisms of `ProEtale.CondensedRing.finiteFreeTransition` on the
  fibre products (`finiteFreeTransition_hom_eq`, `finiteFreeTransition_inv_eq`).

For a family of trivialisations, these properties are packaged in
`ProEtale.CondensedRing.exists_frameTransitions`, which hides the transition morphisms behind an
existential: downstream statements then only involve an opaque family of morphisms.

The compatibility with precomposition rests on the cocycle condition for the identifications
`g^* Λ_Y ≅ Λ_X` (`upperStarObjRegularIso_comp`), which are the inverses of the unit comparisons
of the strong monoidal pullbacks (`upperStarObjRegularIso_hom_eq`).

We also record the matrix calculus of morphisms of free module objects: the entries of a
composite are the matrix products of the entries (`CategoryTheory.Mod.finFreeMatrix_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The matrix of a morphism `Rᵐ ⟶ Rⁿ` of free module objects, with entries in the
endomorphisms of the regular module. -/
noncomputable def finFreeMatrix {m n : ℕ} (φ : finiteFree R m ⟶ finiteFree R n) :
    Matrix (Fin n) (Fin m) (End (regular R)) :=
  Matrix.of fun a b ↦ finFreeEntry φ a b

omit [PreservesFiniteColimits (tensorLeft R)] in
lemma finFreeMatrix_apply {m n : ℕ} (φ : finiteFree R m ⟶ finiteFree R n) (a : Fin n)
    (b : Fin m) : finFreeMatrix φ a b = finFreeEntry φ a b :=
  rfl

omit [PreservesFiniteColimits (tensorLeft R)] in
/-- **The matrix of a composite is the product of the matrices.** -/
lemma finFreeMatrix_comp {l m n : ℕ} (φ : finiteFree R l ⟶ finiteFree R m)
    (ψ : finiteFree R m ⟶ finiteFree R n) :
    finFreeMatrix (φ ≫ ψ) = finFreeMatrix ψ * finFreeMatrix φ := by
  apply Matrix.ext
  intro a c
  apply End.ext
  rw [Matrix.mul_apply, End.sum_asHom, finFreeMatrix_apply, finFreeEntry]
  have : φ ≫ ψ = φ ≫ (∑ b, biproduct.π (fun _ : Fin m ↦ regular R) b ≫
      biproduct.ι (fun _ : Fin m ↦ regular R) b) ≫ ψ := by
    rw [biproduct.total, Category.id_comp]
  rw [this, Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  dsimp only
  apply Finset.sum_congr rfl
  intro b _
  rw [finFreeMatrix_apply, finFreeMatrix_apply, End.mul_asHom, finFreeEntry, finFreeEntry]
  simp only [Category.assoc]

omit [PreservesFiniteColimits (tensorLeft R)] in
/-- The matrix of the identity is the identity matrix. -/
lemma finFreeMatrix_id {n : ℕ} : finFreeMatrix (𝟙 (finiteFree R n)) = 1 := by
  apply Matrix.ext
  intro a b
  apply End.ext
  rw [finFreeMatrix_apply, finFreeEntry, Category.id_comp, Matrix.one_apply]
  by_cases h : b = a
  · subst h
    rw [biproduct.ι_π_self, ite_eq_left rfl]
    rfl
  · rw [biproduct.ι_π_ne _ h, ite_eq_right (Ne.symm h)]
    rfl

omit [PreservesFiniteColimits (tensorLeft R)] in
/-- A morphism of free module objects is determined by its matrix. -/
lemma finFreeMatrix_injective {m n : ℕ} {φ ψ : finiteFree R m ⟶ finiteFree R n}
    (h : finFreeMatrix φ = finFreeMatrix ψ) : φ = ψ :=
  finFree_hom_ext fun a b ↦ congrFun (congrFun h a) b

/-- The morphism of free module objects with a given matrix. -/
noncomputable def finFreeOfMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) (End (regular R))) :
    finiteFree R m ⟶ finiteFree R n :=
  biproduct.matrix fun b a ↦ (A a b).asHom

omit [PreservesFiniteColimits (tensorLeft R)] in
@[simp]
lemma finFreeMatrix_finFreeOfMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) (End (regular R))) :
    finFreeMatrix (finFreeOfMatrix A) = A := by
  apply Matrix.ext
  intro a b
  apply End.ext
  simp [finFreeMatrix_apply, finFreeEntry, finFreeOfMatrix]

/-- The isomorphism of free module objects with a given invertible matrix. -/
noncomputable def finFreeIsoOfMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) (End (regular R)))
    (hAB : A * B = 1) (hBA : B * A = 1) : finiteFree R n ≅ finiteFree R n where
  hom := finFreeOfMatrix A
  inv := finFreeOfMatrix B
  hom_inv_id := finFreeMatrix_injective (by
    rw [finFreeMatrix_comp, finFreeMatrix_finFreeOfMatrix, finFreeMatrix_finFreeOfMatrix, hBA,
      finFreeMatrix_id])
  inv_hom_id := finFreeMatrix_injective (by
    rw [finFreeMatrix_comp, finFreeMatrix_finFreeOfMatrix, finFreeMatrix_finFreeOfMatrix, hAB,
      finFreeMatrix_id])

omit [PreservesFiniteColimits (tensorLeft R)] in
@[simp]
lemma finFreeIsoOfMatrix_hom {n : ℕ} (A B : Matrix (Fin n) (Fin n) (End (regular R)))
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (finFreeIsoOfMatrix A B hAB hBA).hom = finFreeOfMatrix A :=
  rfl

omit [PreservesFiniteColimits (tensorLeft R)] in
@[simp]
lemma finFreeIsoOfMatrix_inv {n : ℕ} (A B : Matrix (Fin n) (Fin n) (End (regular R)))
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (finFreeIsoOfMatrix A B hAB hBA).inv = finFreeOfMatrix B :=
  rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The identifications `g^* Λ_Y ≅ Λ_X` -/

section RegularIso

/-- The identification `g^* Λ_Y ≅ Λ_X` of the pullback of the regular module is the inverse of
the unit comparison of the strong monoidal pullback `g^*`: both are adjoint to `η_g`. -/
lemma upperStarObjRegularIso_hom_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStarObjRegularIso Λ g).hom = (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv := by
  apply ((upperStarLowerStarAdjunction Λ g).homEquiv _ _).injective
  ext1
  refine (upperStarLowerStarAdjunction_homEquiv_hom Λ g _ _ _).trans ?_
  rw [extendUnitHom_upperStarObjRegularIso_hom]
  exact (unitAlgHom_comp_map_condensedPullbackHom Λ g).trans (homEquiv_εIso_inv_hom Λ g).symm

/-- **Cocycle condition** for the identifications `g^* Λ_Y ≅ Λ_X`. -/
lemma upperStarObjRegularIso_comp {Q P W : Scheme.{u}} (c : Q ⟶ P) (a : P ⟶ W) :
    (upperStarComp Λ c a).hom.app (Mod.regular (condensedRingObj Λ W)) ≫
        (c)^*⟦Λ⟧.map (upperStarObjRegularIso Λ a).hom ≫ (upperStarObjRegularIso Λ c).hom =
      (upperStarObjRegularIso Λ (c ≫ a)).hom := by
  simp only [upperStarObjRegularIso_hom_eq]
  exact upperStarComp_hom_app_unit Λ c a

/-- **Cocycle condition** for the identifications `g^* Λ_Yⁿ ≅ Λ_Xⁿ`. -/
lemma upperStarFiniteFreeIso_comp {Q P W : Scheme.{u}} (c : Q ⟶ P) (a : P ⟶ W) (n : ℕ) :
    (upperStarFiniteFreeIso Λ (c ≫ a) n).hom =
      (upperStarComp Λ c a).hom.app _ ≫ (c)^*⟦Λ⟧.map (upperStarFiniteFreeIso Λ a n).hom ≫
        (upperStarFiniteFreeIso Λ c n).hom := by
  refine Functor.map_biproduct_hom_ext (c ≫ a)^*⟦Λ⟧ fun i ↦ ?_
  have hn := (upperStarComp Λ c a).hom.naturality
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ W)) i)
  simp only [Functor.comp_map] at hn
  rw [upperStarFiniteFreeIso, Mod.map_ι_comp_finiteFreeIsoMap_hom, reassoc_of% hn,
    ← Functor.map_comp_assoc, upperStarFiniteFreeIso, Mod.map_ι_comp_finiteFreeIsoMap_hom,
    Functor.map_comp_assoc, upperStarFiniteFreeIso, Mod.map_ι_comp_finiteFreeIsoMap_hom,
    reassoc_of% (upperStarObjRegularIso_comp Λ c a)]

end RegularIso

/-! ### Congruences -/

section Congr

/-- The inverse of a congruence isomorphism is a congruence isomorphism. -/
lemma upperStarCongr_inv_app {X Z : Scheme.{u}} {x y : X ⟶ Z} (p : x = y) (q : y = x)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarCongr Λ p).inv.app M = (upperStarCongr Λ q).hom.app M := by
  subst p
  rfl

/-- The pullback of a congruence isomorphism is a congruence isomorphism. -/
lemma upperStarComp_inv_app_comp_congr_comp_hom_app {Q X Z : Scheme.{u}} (c : Q ⟶ X)
    {x y : X ⟶ Z} (p : x = y) (p' : c ≫ x = c ≫ y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarComp Λ c x).inv.app M ≫ (upperStarCongr Λ p').hom.app M ≫
        (upperStarComp Λ c y).hom.app M =
      (c)^*⟦Λ⟧.map ((upperStarCongr Λ p).hom.app M) := by
  subst p
  simp [upperStarCongr_self]

/-- The congruence isomorphisms compose. The composite equality is an independent hypothesis,
so that no new equality proofs are built (comparing such proofs can make the kernel time out). -/
@[reassoc]
lemma upperStarCongr_hom_app_trans' {X Z : Scheme.{u}} {x y z : X ⟶ Z} (p : x = y) (p' : y = z)
    (p'' : x = z) (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarCongr Λ p).hom.app M ≫ (upperStarCongr Λ p').hom.app M =
      (upperStarCongr Λ p'').hom.app M := by
  subst p p'
  simp [upperStarCongr_self]

/-- A congruence isomorphism along `x = x` is the identity. -/
lemma upperStarCongr_hom_app_self {X Z : Scheme.{u}} {x : X ⟶ Z} (p : x = x)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarCongr Λ p).hom.app M = 𝟙 _ := by
  rw [upperStarCongr_self]
  rfl

/-- The congruence isomorphism does not depend on the proof of the equality; rewriting with this
lemma replaces one proof by another syntactically. -/
lemma upperStarCongr_hom_app_congr {X Z : Scheme.{u}} {x y : X ⟶ Z} (p q : x = y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarCongr Λ p).hom.app M = (upperStarCongr Λ q).hom.app M := by
  subst p
  rw [upperStarCongr_hom_app_self]

end Congr

/-! ### Transition morphisms

We do not introduce definitions for the frames and transition morphisms: unfolding a definition
whose body contains instance arguments of the pullbacks of module objects against the same
term elaborated in a statement is very expensive (the auxiliary proofs abstracted from the body
differ from those of the statement). The transition morphism of `e, e'` at `a, b` is written out
as the composite
```
Λ_Wⁿ ≅ a^* Λ_Vⁿ --a^* e--> a^* f^* L ≅ (a ≫ f)^* L = (b ≫ f')^* L ≅ b^* f'^* L --b^* e'⁻¹-->
  b^* Λ_V'ⁿ' ≅ Λ_Wⁿ'.
```
-/

section Transition

variable {S V V' V'' W : Scheme.{u}}
  {L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
  {f : V ⟶ S} {f' : V' ⟶ S} {f'' : V'' ⟶ S} {n n' n'' : ℕ}
  (e : Mod.finiteFree (condensedRingObj Λ V) n ≅ (f)^*⟦Λ⟧.obj L)
  (e' : Mod.finiteFree (condensedRingObj Λ V') n' ≅ (f')^*⟦Λ⟧.obj L)
  (e'' : Mod.finiteFree (condensedRingObj Λ V'') n'' ≅ (f'')^*⟦Λ⟧.obj L)

/-- **Transition morphisms compose.** -/
lemma frameTransition_trans (a : W ⟶ V) (b : W ⟶ V') (c : W ⟶ V'') (h : a ≫ f = b ≫ f')
    (h' : b ≫ f' = c ≫ f'') (h'' : a ≫ f = c ≫ f'') :
    ((upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ b n').hom) ≫
      ((upperStarFiniteFreeIso Λ b n').inv ≫ (b)^*⟦Λ⟧.map e'.hom ≫
        (upperStarComp Λ b f').inv.app L ≫ (upperStarCongr Λ h').hom.app L ≫
        (upperStarComp Λ c f'').hom.app L ≫ (c)^*⟦Λ⟧.map e''.inv ≫
        (upperStarFiniteFreeIso Λ c n'').hom) =
    (upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h'').hom.app L ≫
        (upperStarComp Λ c f'').hom.app L ≫ (c)^*⟦Λ⟧.map e''.inv ≫
        (upperStarFiniteFreeIso Λ c n'').hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc, upperStarCongr_hom_app_trans'_assoc Λ h h' h'']

/-- The transition morphism of a trivialisation with itself along a morphism is the identity. -/
lemma frameTransition_self (a : W ⟶ V) (h : a ≫ f = a ≫ f) :
    (upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ a f).hom.app L ≫ (a)^*⟦Λ⟧.map e.inv ≫
        (upperStarFiniteFreeIso Λ a n).hom = 𝟙 _ := by
  rw [upperStarCongr_hom_app_self, Category.id_comp, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

/-- Transition morphisms only depend on the morphisms. -/
lemma frameTransition_congr {a a₁ : W ⟶ V} {b b₁ : W ⟶ V'} (ha : a = a₁) (hb : b = b₁)
    (h : a ≫ f = b ≫ f') (h₁ : a₁ ≫ f = b₁ ≫ f') :
    (upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ b n').hom =
      (upperStarFiniteFreeIso Λ a₁ n).inv ≫ (a₁)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a₁ f).inv.app L ≫ (upperStarCongr Λ h₁).hom.app L ≫
        (upperStarComp Λ b₁ f').hom.app L ≫ (b₁)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ b₁ n').hom := by
  subst ha hb
  obtain rfl : h = h₁ := rfl
  rfl

/-- The pullback of a trivialisation along a composite. -/
lemma upperStarFrame_comp {Q : Scheme.{u}} (c : Q ⟶ W) (a : W ⟶ V) :
    (upperStarFiniteFreeIso Λ (c ≫ a) n).inv ≫ (c ≫ a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ (c ≫ a) f).inv.app L =
      (upperStarFiniteFreeIso Λ c n).inv ≫ (c)^*⟦Λ⟧.map ((upperStarFiniteFreeIso Λ a n).inv ≫
        (a)^*⟦Λ⟧.map e.hom ≫ (upperStarComp Λ a f).inv.app L) ≫
        (upperStarComp Λ c (a ≫ f)).inv.app L ≫
        (upperStarCongr Λ (Category.assoc c a f).symm).hom.app L := by
  have h₁ : (upperStarFiniteFreeIso Λ (c ≫ a) n).inv = (upperStarFiniteFreeIso Λ c n).inv ≫
      (c)^*⟦Λ⟧.map (upperStarFiniteFreeIso Λ a n).inv ≫ (upperStarComp Λ c a).inv.app _ := by
    rw [← cancel_epi (upperStarFiniteFreeIso Λ (c ≫ a) n).hom, Iso.hom_inv_id,
      upperStarFiniteFreeIso_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  have h₂ := (upperStarComp Λ c a).hom.naturality e.hom
  simp only [Functor.comp_map] at h₂
  have h₂' : (upperStarComp Λ c a).inv.app _ ≫ (c ≫ a)^*⟦Λ⟧.map e.hom =
      (c)^*⟦Λ⟧.map ((a)^*⟦Λ⟧.map e.hom) ≫ (upperStarComp Λ c a).inv.app _ := by
    rw [← cancel_epi ((upperStarComp Λ c a).hom.app _), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% h₂, Iso.hom_inv_id_app, Category.comp_id]
  have h₃ := upperStarComp_hom_app_comp_upperStarComp_hom_app Λ c a f L
  have h₃' : (upperStarComp Λ c a).inv.app ((f)^*⟦Λ⟧.obj L) ≫
      (upperStarComp Λ (c ≫ a) f).inv.app L =
      (c)^*⟦Λ⟧.map ((upperStarComp Λ a f).inv.app L) ≫ (upperStarComp Λ c (a ≫ f)).inv.app L ≫
        (upperStarCongr Λ (Category.assoc c a f).symm).hom.app L := by
    rw [← cancel_epi ((upperStarComp Λ (c ≫ a) f).hom.app L ≫
      (upperStarComp Λ c a).hom.app ((f)^*⟦Λ⟧.obj L))]
    conv_lhs => rw [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [h₃]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    rw [upperStarCongr_hom_app_trans' Λ _ _ rfl, upperStarCongr_hom_app_self]
  rw [h₁]
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% h₂', h₃']

/-- **Transition morphisms are compatible with precomposition**: the transition morphism at
`c ≫ a, c ≫ b` is the pullback along `c` of the transition morphism at `a, b`. -/
lemma frameTransition_comp {Q : Scheme.{u}} (c : Q ⟶ W) (a : W ⟶ V) (b : W ⟶ V')
    (h : a ≫ f = b ≫ f') (h' : (c ≫ a) ≫ f = (c ≫ b) ≫ f') :
    (upperStarFiniteFreeIso Λ (c ≫ a) n).inv ≫ (c ≫ a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ (c ≫ a) f).inv.app L ≫ (upperStarCongr Λ h').hom.app L ≫
        (upperStarComp Λ (c ≫ b) f').hom.app L ≫ (c ≫ b)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ (c ≫ b) n').hom =
      (upperStarFiniteFreeIso Λ c n).inv ≫ (c)^*⟦Λ⟧.map ((upperStarFiniteFreeIso Λ a n).inv ≫
        (a)^*⟦Λ⟧.map e.hom ≫ (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ b n').hom) ≫ (upperStarFiniteFreeIso Λ c n').hom := by
  have hb := upperStarFrame_comp Λ e' c b
  have hinv : (upperStarComp Λ (c ≫ b) f').hom.app L ≫ (c ≫ b)^*⟦Λ⟧.map e'.inv ≫
      (upperStarFiniteFreeIso Λ (c ≫ b) n').hom =
      (upperStarCongr Λ (Category.assoc c b f')).hom.app L ≫
        (upperStarComp Λ c (b ≫ f')).hom.app L ≫ (c)^*⟦Λ⟧.map
          ((upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map e'.inv ≫
            (upperStarFiniteFreeIso Λ b n').hom) ≫ (upperStarFiniteFreeIso Λ c n').hom := by
    rw [← cancel_epi ((upperStarFiniteFreeIso Λ (c ≫ b) n').inv ≫ (c ≫ b)^*⟦Λ⟧.map e'.hom ≫
      (upperStarComp Λ (c ≫ b) f').inv.app L)]
    conv_lhs => rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
    rw [hb]
    simp only [Category.assoc]
    rw [upperStarCongr_hom_app_trans'_assoc Λ _ _ rfl, upperStarCongr_hom_app_self,
      Category.id_comp, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
  have p : c ≫ a ≫ f = c ≫ b ≫ f' := by rw [h]
  have q : c ≫ a ≫ f = (c ≫ b) ≫ f' := by rw [h, Category.assoc]
  have hc := upperStarComp_inv_app_comp_congr_comp_hom_app Λ c h p L
  rw [hinv, reassoc_of% (upperStarFrame_comp Λ e c a)]
  simp only [Category.assoc, Functor.map_comp]
  rw [upperStarCongr_hom_app_trans'_assoc Λ _ _ q, upperStarCongr_hom_app_trans'_assoc Λ _ _ p,
    reassoc_of% hc]

/-- The transition isomorphisms on a fibre product are the transition morphisms at the
projections, through `p^* Λ_Vⁿ ≅ Λ_Pⁿ`. -/
lemma finiteFreeTransition_hom_eq {P : Scheme.{u}} {p₁ : P ⟶ V} {p₂ : P ⟶ V'}
    (hP : IsPullback p₁ p₂ f f') :
    (finiteFreeTransition hP e e').hom = (upperStarFiniteFreeIso Λ p₁ n).hom ≫
      ((upperStarFiniteFreeIso Λ p₁ n).inv ≫ (p₁)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ p₁ f).inv.app L ≫ (upperStarCongr Λ hP.flip.toCommSq.w.symm).hom.app L ≫
        (upperStarComp Λ p₂ f').hom.app L ≫ (p₂)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ p₂ n').hom) ≫ (upperStarFiniteFreeIso Λ p₂ n').inv := by
  rw [← cancel_mono ((p₂)^*⟦Λ⟧.map e'.hom), ← upperStar_map_hom_comp_finiteFreeTransition,
    upperStarSquareComparison_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- The inverses of the transition isomorphisms on a fibre product are the transition morphisms
at the projections in the other order. -/
lemma finiteFreeTransition_inv_eq {P : Scheme.{u}} {p₁ : P ⟶ V} {p₂ : P ⟶ V'}
    (hP : IsPullback p₁ p₂ f f') :
    (finiteFreeTransition hP e e').inv = (upperStarFiniteFreeIso Λ p₂ n').hom ≫
      ((upperStarFiniteFreeIso Λ p₂ n').inv ≫ (p₂)^*⟦Λ⟧.map e'.hom ≫
        (upperStarComp Λ p₂ f').inv.app L ≫ (upperStarCongr Λ hP.flip.toCommSq.w).hom.app L ≫
        (upperStarComp Λ p₁ f).hom.app L ≫ (p₁)^*⟦Λ⟧.map e.inv ≫
        (upperStarFiniteFreeIso Λ p₁ n).hom) ≫ (upperStarFiniteFreeIso Λ p₁ n).inv := by
  refine Iso.inv_ext ?_
  have htr := frameTransition_trans Λ e e' e p₁ p₂ p₁ hP.flip.toCommSq.w.symm
    hP.flip.toCommSq.w rfl
  rw [frameTransition_self] at htr
  rw [finiteFreeTransition_hom_eq]
  simp only [Category.assoc] at htr ⊢
  rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 15 => rw [htr]
  rw [Category.id_comp, Iso.hom_inv_id]

/-- Changing two trivialisations by automorphisms of the free modules changes their transition
morphisms by the pullbacks of the automorphisms. -/
lemma frameTransition_trans_iso
    (G : Mod.finiteFree (condensedRingObj Λ V) n ≅ Mod.finiteFree (condensedRingObj Λ V) n)
    (G' : Mod.finiteFree (condensedRingObj Λ V') n' ≅ Mod.finiteFree (condensedRingObj Λ V') n')
    (a : W ⟶ V) (b : W ⟶ V') (h : a ≫ f = b ≫ f') :
    (upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map (G ≪≫ e).hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map (G' ≪≫ e').inv ≫
        (upperStarFiniteFreeIso Λ b n').hom =
      ((upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map G.hom ≫
        (upperStarFiniteFreeIso Λ a n).hom) ≫
      ((upperStarFiniteFreeIso Λ a n).inv ≫ (a)^*⟦Λ⟧.map e.hom ≫
        (upperStarComp Λ a f).inv.app L ≫ (upperStarCongr Λ h).hom.app L ≫
        (upperStarComp Λ b f').hom.app L ≫ (b)^*⟦Λ⟧.map e'.inv ≫
        (upperStarFiniteFreeIso Λ b n').hom) ≫
      ((upperStarFiniteFreeIso Λ b n').inv ≫ (b)^*⟦Λ⟧.map G'.inv ≫
        (upperStarFiniteFreeIso Λ b n').hom) := by
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end Transition
/-- The matrix of the pullback of a morphism of free module objects is the restriction of its
matrix. -/
lemma finFreeMatrix_upperStar {W' W : Scheme.{u}} (g : W' ⟶ W) {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ W) m ⟶ Mod.finiteFree (condensedRingObj Λ W) n) :
    Mod.finFreeMatrix ((upperStarFiniteFreeIso Λ g m).inv ≫ (g)^*⟦Λ⟧.map φ ≫
      (upperStarFiniteFreeIso Λ g n).hom) = (Mod.finFreeMatrix φ).map (restrictEnd Λ g) := by
  exact Matrix.ext (ι_upperStarFinFreeMap_π Λ g φ)
/-- The entries `(p^* Λ_V ≅ Λ_P ⟶ ...)` appearing in `ProEtale.CondensedRing.IsDefinedOver` of a
morphism `p^* Λ_Vⁿ ⟶ p'^* Λ_V'ᵐ` which is, through `p^* Λ_Vⁿ ≅ Λ_Pⁿ`, a morphism `φ` of free
module objects are the entries of `φ`. -/
lemma upperStarObjRegularIso_inv_comp_map_ι_comp {P V V' : Scheme.{u}} (p : P ⟶ V)
    (p' : P ⟶ V') {n m : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ P) n ⟶ Mod.finiteFree (condensedRingObj Λ P) m)
    (i : Fin n) (j : Fin m) :
    (upperStarObjRegularIso Λ p).inv ≫
        (p)^*⟦Λ⟧.map (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ V)) i) ≫
        ((upperStarFiniteFreeIso Λ p n).hom ≫ φ ≫ (upperStarFiniteFreeIso Λ p' m).inv) ≫
        (p')^*⟦Λ⟧.map (biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ V')) j) ≫
        (upperStarObjRegularIso Λ p').hom = (Mod.finFreeEntry φ j i).asHom := by
  have h₁ : (upperStarFiniteFreeIso Λ p' m).inv ≫
      (p')^*⟦Λ⟧.map (biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ V')) j) ≫
      (upperStarObjRegularIso Λ p').hom =
      biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ P)) j := by
    rw [← cancel_epi (upperStarFiniteFreeIso Λ p' m).hom, Iso.hom_inv_id_assoc,
      upperStarFiniteFreeIso, Mod.finiteFreeIsoMap_hom_comp_π]
  simp only [Category.assoc]
  rw [h₁, upperStarFiniteFreeIso, Mod.map_ι_comp_finiteFreeIsoMap_hom_assoc, Iso.inv_hom_id_assoc,
    Mod.finFreeEntry]

/-! ### Transition morphisms of a family of trivialisations -/

section Family

variable {Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₀]
  (a : Λ₀ ⟶ Λ) [IsMonHom a]

/-- A morphism `p^* Λ_Vⁿ ⟶ p'^* Λ_V'ᵐ` which is, through `p^* Λ_Vⁿ ≅ Λ_Pⁿ`, a morphism `φ` of
free module objects is defined over `Λ₀` as soon as the entries of `φ` are. -/
lemma isDefinedOver_of_finFreeEntry {P V V' : Scheme.{u}} (p : P ⟶ V) (p' : P ⟶ V') {n m : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ P) n ⟶ Mod.finiteFree (condensedRingObj Λ P) m)
    (hφ : ∀ i j, ∃ t : Γ (condensedRingObj Λ₀ P),
      Mod.finFreeEntry φ j i = Mod.regularEndRingHom (Γ.map (coefficientMap a P) t)) :
    IsDefinedOver a p p'
      ((upperStarFiniteFreeIso Λ p n).hom ≫ φ ≫ (upperStarFiniteFreeIso Λ p' m).inv) := by
  intro i j
  obtain ⟨t, ht⟩ := hφ i j
  refine ⟨t, ?_⟩
  rw [upperStarObjRegularIso_inv_comp_map_ι_comp, ht]

/-- **Transition morphisms of a family of trivialisations.** For trivialisations
`e_k : Λ_{V_k}ⁿ ≅ f_k^* L`, there are morphisms `T j k W a b h : Λ_Wⁿ ⟶ Λ_Wⁿ` (the transition
from the pullback of `e_k` along `b` to the pullback of `e_j` along `a`) which compose, are the
identity for `j = k`, `a = b`, are compatible with precomposition on matrices, and compute the
transition isomorphisms of trivialisations changed by automorphisms `G_k`: if the entries of the
conjugated transition morphisms are defined over `Λ₀`, so are the transition isomorphisms. -/
theorem exists_frameTransitions {κ : Type*} {S : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    {V : κ → Scheme.{u}} (f : ∀ k, V k ⟶ S) {n : ℕ}
    (e : ∀ k, Mod.finiteFree (condensedRingObj Λ (V k)) n ≅ (f k)^*⟦Λ⟧.obj L) :
    ∃ T : ∀ (j k : κ) (W : Scheme.{u}) (a : W ⟶ V j) (b : W ⟶ V k), a ≫ f j = b ≫ f k →
        (Mod.finiteFree (condensedRingObj Λ W) n ⟶ Mod.finiteFree (condensedRingObj Λ W) n),
      (∀ (j k l : κ) (W : Scheme.{u}) (a : W ⟶ V j) (b : W ⟶ V k) (c : W ⟶ V l)
        (h : a ≫ f j = b ≫ f k) (h' : b ≫ f k = c ≫ f l) (h'' : a ≫ f j = c ≫ f l),
        T k l W b c h' ≫ T j k W a b h = T j l W a c h'') ∧
      (∀ (k : κ) (W : Scheme.{u}) (a : W ⟶ V k) (h : a ≫ f k = a ≫ f k), T k k W a a h = 𝟙 _) ∧
      (∀ (j k : κ) (W W' : Scheme.{u}) (c : W' ⟶ W) (a : W ⟶ V j) (b : W ⟶ V k)
        (h : a ≫ f j = b ≫ f k) (h' : (c ≫ a) ≫ f j = (c ≫ b) ≫ f k),
        Mod.finFreeMatrix (T j k W' (c ≫ a) (c ≫ b) h') =
          (Mod.finFreeMatrix (T j k W a b h)).map (restrictEnd Λ c)) ∧
      ∀ (G : ∀ k, Mod.finiteFree (condensedRingObj Λ (V k)) n ≅
          Mod.finiteFree (condensedRingObj Λ (V k)) n) (j k : κ) {P : Scheme.{u}}
        {p₁ : P ⟶ V j} {p₂ : P ⟶ V k} (hP : IsPullback p₁ p₂ (f j) (f k)),
        ((∀ i i', ∃ t : Γ (condensedRingObj Λ₀ P),
          Mod.finFreeEntry (Mod.finFreeOfMatrix ((Mod.finFreeMatrix (G k).inv).map
            (restrictEnd Λ p₂) * Mod.finFreeMatrix (T k j P p₂ p₁ hP.w.symm) *
              (Mod.finFreeMatrix (G j).hom).map (restrictEnd Λ p₁))) i' i =
            Mod.regularEndRingHom (Γ.map (coefficientMap a P) t)) →
          IsDefinedOver a p₁ p₂ (finiteFreeTransition hP (G j ≪≫ e j) (G k ≪≫ e k)).hom) ∧
        ((∀ i i', ∃ t : Γ (condensedRingObj Λ₀ P),
          Mod.finFreeEntry (Mod.finFreeOfMatrix ((Mod.finFreeMatrix (G j).inv).map
            (restrictEnd Λ p₁) * Mod.finFreeMatrix (T j k P p₁ p₂ hP.w) *
              (Mod.finFreeMatrix (G k).hom).map (restrictEnd Λ p₂))) i' i =
            Mod.regularEndRingHom (Γ.map (coefficientMap a P) t)) →
          IsDefinedOver a p₂ p₁ (finiteFreeTransition hP (G j ≪≫ e j) (G k ≪≫ e k)).inv) := by
  refine ⟨fun j k W a b h ↦ (upperStarFiniteFreeIso Λ b n).inv ≫ (b)^*⟦Λ⟧.map (e k).hom ≫
      (upperStarComp Λ b (f k)).inv.app L ≫ (upperStarCongr Λ h.symm).hom.app L ≫
      (upperStarComp Λ a (f j)).hom.app L ≫ (a)^*⟦Λ⟧.map (e j).inv ≫
      (upperStarFiniteFreeIso Λ a n).hom, ?_, ?_, ?_, ?_⟩
  · intro j k l W a b c h h' h''
    exact frameTransition_trans Λ (e l) (e k) (e j) c b a h'.symm h.symm h''.symm
  · intro k W a h
    exact frameTransition_self Λ (e k) a h.symm
  · intro j k W W' c a b h h'
    beta_reduce
    rw [frameTransition_comp Λ (e k) (e j) c b a h.symm h'.symm, finFreeMatrix_upperStar]
  · intro G j k P p₁ p₂ hP
    refine ⟨fun hent ↦ ?_, fun hent ↦ ?_⟩
    · have H := finiteFreeTransition_hom_eq Λ (G j ≪≫ e j) (G k ≪≫ e k) hP
      rw [frameTransition_trans_iso Λ (e j) (e k) (G j) (G k) p₁ p₂ hP.flip.toCommSq.w.symm,
        upperStarCongr_hom_app_congr Λ hP.flip.toCommSq.w.symm hP.w.symm.symm] at H
      rw [H]
      refine isDefinedOver_of_finFreeEntry Λ a p₁ p₂ _ fun i i' ↦ ?_
      obtain ⟨t, ht⟩ := hent i i'
      refine ⟨t, ?_⟩
      rw [← ht, ← Mod.finFreeMatrix_apply, ← Mod.finFreeMatrix_apply,
        Mod.finFreeMatrix_finFreeOfMatrix, Mod.finFreeMatrix_comp, Mod.finFreeMatrix_comp,
        finFreeMatrix_upperStar, finFreeMatrix_upperStar]
    · have H := finiteFreeTransition_inv_eq Λ (G j ≪≫ e j) (G k ≪≫ e k) hP
      rw [frameTransition_trans_iso Λ (e k) (e j) (G k) (G j) p₂ p₁ hP.flip.toCommSq.w,
        upperStarCongr_hom_app_congr Λ hP.flip.toCommSq.w hP.w.symm] at H
      rw [H]
      refine isDefinedOver_of_finFreeEntry Λ a p₂ p₁ _ fun i i' ↦ ?_
      obtain ⟨t, ht⟩ := hent i i'
      refine ⟨t, ?_⟩
      rw [← ht, ← Mod.finFreeMatrix_apply, ← Mod.finFreeMatrix_apply,
        Mod.finFreeMatrix_finFreeOfMatrix, Mod.finFreeMatrix_comp, Mod.finFreeMatrix_comp,
        finFreeMatrix_upperStar, finFreeMatrix_upperStar]

end Family

end AlgebraicGeometry.ProEtale.CondensedRing
