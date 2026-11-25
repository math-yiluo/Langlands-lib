/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomDual
public import WeilConjectures.WeilSheaf.StalkTensor

/-!
# The pairing `F ⊗ G ⟶ F ⊗ G` of Weil sheaves

For a lisse Weil sheaf `F` and a Weil sheaf `G`, the tensor product `F ⊗ G` is the internal hom
`𝓗om(F^∨, G)` (`AlgebraicGeometry.WeilSheaf.tensorObj`). The morphism of underlying sheaves
`F ⊗ G ⟶ 𝓗om(F^∨, G)`, `f ⊗ g ↦ (φ ↦ φ(f) g)` (`CategoryTheory.Mod.toIhomDual`), is compatible
with the Weil structures (`AlgebraicGeometry.WeilSheaf.toIhomDual_str`): its uncurried form is
built from the evaluation `F^∨ ⊗ F ⟶ ℚ̄_ℓ` and the action `ℚ̄_ℓ ⊗ G ⟶ G`, both compatible with the
Weil structures, and morphisms into an internal hom are determined by their uncurried form.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] (G : C ⥤ C)
  [G.LaxBraided]

/-- The morphism `(m ⊗ n) ⊗ d ↦ a (e (d ⊗ m) ⊗ n)` is compatible with morphisms
`G X ⟶ X` with which `e` and `a` are compatible, for a lax braided endofunctor `G`. -/
lemma tensorHom_comp_braiding_comp_associator_inv_comp {M N D A : C} (φM : G.obj M ⟶ M)
    (φN : G.obj N ⟶ N) (φD : G.obj D ⟶ D) (φA : G.obj A ⟶ A) (e : D ⊗ M ⟶ A) (a : A ⊗ N ⟶ N)
    (he : (φD ⊗ₘ φM) ≫ e = μ G D M ≫ G.map e ≫ φA)
    (ha : (φA ⊗ₘ φN) ≫ a = μ G A N ≫ G.map a ≫ φN) :
    ((φM ⊗ₘ φN) ⊗ₘ φD) ≫ (β_ (M ⊗ N) D).hom ≫ (α_ D M N).inv ≫ e ▷ N ≫ a =
      μ G M N ▷ G.obj D ≫ μ G (M ⊗ N) D ≫
        G.map ((β_ (M ⊗ N) D).hom ≫ (α_ D M N).inv ≫ e ▷ N ≫ a) ≫ φN := by
  rw [BraidedCategory.braiding_naturality_assoc, associator_inv_naturality_assoc,
    tensorHom_def'_assoc (φD ⊗ₘ φM), ← comp_whiskerRight_assoc, he]
  simp only [comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← tensorHom_def_assoc, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [LaxBraided.braided_assoc, BraidedCategory.braiding_naturality_left_assoc,
    associativity_inv_assoc, μ_natural_left_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open ProEtale

/-- The action `ℚ̄_ℓ ⊗ G ⟶ G` is compatible with the Weil structures of `ℚ̄_ℓ` and of `G`. -/
lemma act_str (G : WeilSheaf k₀ l X) :
    ((adicConstant k₀ l X).obj.str.hom.hom ⊗ₘ G.obj.str.hom.hom) ≫
        Mod.act (A := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          G.obj.carrier.X =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l]
          _ G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.act (A := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
            G.obj.carrier.X) ≫ G.obj.str.hom.hom := by
  have h := Mod.act_hom G.obj.str.hom
  have hact : Mod.act ((frobeniusPullback k₀ l X).obj G.obj.carrier).X =
      adicConstantSheafToLowerStar l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ▷ _ ≫
        μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l]
          _ G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.act G.obj.carrier.X) := rfl
  rw [hact] at h
  rw [adicConstant_str_hom_hom, tensorHom_def, Category.assoc]
  erw [← h]
  simp only [Category.assoc]
  erw [← comp_whiskerRight_assoc, Iso.hom_inv_id]
  rw [id_whiskerRight, Category.id_comp]

/-- **The pairing `F ⊗ G ⟶ F ⊗ G` is compatible with the Weil structures.** The morphism of
underlying sheaves `F ⊗ G ⟶ 𝓗om(F^∨, G)`, `f ⊗ g ↦ (φ ↦ φ(f) g)`, intertwines the Weil
structures of `F`, `G` and of the tensor product `F ⊗ G = 𝓗om(F^∨, G)`. -/
theorem toIhomDual_str (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    (F.obj.str.hom.hom ⊗ₘ G.obj.str.hom.hom) ≫
        Mod.toIhomDual F.obj.carrier G.obj.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l]
          F.obj.carrier.X G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.toIhomDual F.obj.carrier G.obj.carrier) ≫
        (F.tensorObj G hF).obj.str.hom.hom := by
  set Fr :=
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
  have : IsIso (F.dual hF).obj.str.hom.hom :=
    inferInstanceAs (IsIso ((Mod.forget _).map (F.dual hF).obj.str.hom))
  have hq := Functor.tensorHom_comp_braiding_comp_associator_inv_comp Fr F.obj.str.hom.hom
    G.obj.str.hom.hom (F.dual hF).obj.str.hom.hom (adicConstant k₀ l X).obj.str.hom.hom
    (Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier)
    (Mod.act (A := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      G.obj.carrier.X) (dual_evaluation_str F hF) (act_str G)
  have he := ProEtaleWeilSheaf.ihom_evaluation_str (F.dual hF).obj G.obj
  apply Mod.hom_ext_of_evaluation (D := (F.dual hF).obj.carrier)
  rw [← cancel_epi ((Fr.obj F.obj.carrier.X ⊗ Fr.obj G.obj.carrier.X) ◁
    (F.dual hF).obj.str.hom.hom)]
  rw [comp_whiskerRight_assoc]
  erw [Mod.toIhomDual_evaluation]
  rw [whisker_exchange_assoc, ← tensorHom_def'_assoc]
  erw [hq]
  rw [tensorHom_def (μ Fr _ _ ≫ Fr.map _ ≫ _), comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc, Category.assoc, ← tensorHom_def_assoc]
  erw [he]
  have hμ := μ_natural_left Fr (Mod.toIhomDual F.obj.carrier G.obj.carrier)
    (F.dual hF).obj.carrier.X
  have key : μ Fr F.obj.carrier.X G.obj.carrier.X ▷ Fr.obj (F.dual hF).obj.carrier.X ≫
      Fr.map (Mod.toIhomDual F.obj.carrier G.obj.carrier) ▷ Fr.obj (F.dual hF).obj.carrier.X ≫
      μ Fr _ (F.dual hF).obj.carrier.X ≫
      Fr.map (Mod.evaluation (F.dual hF).obj.carrier G.obj.carrier) ≫ G.obj.str.hom.hom =
      μ Fr F.obj.carrier.X G.obj.carrier.X ▷ Fr.obj (F.dual hF).obj.carrier.X ≫
        μ Fr (F.obj.carrier.X ⊗ G.obj.carrier.X) (F.dual hF).obj.carrier.X ≫
        Fr.map (Mod.toIhomDualAux F.obj.carrier G.obj.carrier) ≫ G.obj.str.hom.hom := by
    rw [reassoc_of% hμ, ← Fr.map_comp_assoc]
    exact congrArg (fun f ↦ μ Fr F.obj.carrier.X G.obj.carrier.X ▷
      Fr.obj (F.dual hF).obj.carrier.X ≫
      μ Fr (F.obj.carrier.X ⊗ G.obj.carrier.X) (F.dual hF).obj.carrier.X ≫ Fr.map f ≫
        G.obj.str.hom.hom) (Mod.toIhomDual_evaluation F.obj.carrier G.obj.carrier)
  exact key.symm

end AlgebraicGeometry.WeilSheaf
