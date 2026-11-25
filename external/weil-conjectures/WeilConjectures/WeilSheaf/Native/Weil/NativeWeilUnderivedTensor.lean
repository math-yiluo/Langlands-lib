/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The existing native tensor as a normalized additive bifunctor

Source: the underived tensor--Hom adjunction and Stacks 06YS, 06YU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private def adjointBifunctor {C : Type a} [Category.{b} C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (L : C → C ⥤ C)
    (adj : ∀ P, L P ⊣ H.obj (op P)) : C ⥤ C ⥤ C where
  obj := L
  map f := (conjugateEquiv (adj _) (adj _)).symm (H.map f.op)
  map_id P := by
    change (conjugateEquiv (adj P) (adj P)).symm (H.map (𝟙 (op P))) = _
    rw [H.map_id]
    exact conjugateEquiv_symm_id (adj P)
  map_comp f g := by
    rw [op_comp, H.map_comp, ← conjugateEquiv_symm_comp]

private def adjointBifunctorAdjunction {C : Type a} [Category.{b} C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (L : C → C ⥤ C)
    (adj : ∀ P, L P ⊣ H.obj (op P)) : adjointBifunctor H L adj ⊣₂ H where
  adj := adj
  unit_whiskerRight_map {P Q} f := by
    ext R
    exact unit_conjugateEquiv_symm (adj Q) (adj P) (H.map f.op) R |>.symm

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

private def tensorBifunctor :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X :=
  adjointBifunctor (ihomBifunctor k₀ l X) (tensorFunctor k₀ l X)
    (tensorIhomAdjunction k₀ l X)

private theorem tensorBifunctor_map {P P' : ProEtaleWeilSheaf k₀ l X}
    (f : P ⟶ P') (Q : ProEtaleWeilSheaf k₀ l X) :
    (((tensorBifunctor k₀ l X).map f).app Q).hom.f =
      (Mod.tensorLeftMap f.hom.f).app Q.carrier := by
  change ((conjugateEquiv (Mod.ihomAdjunction P'.carrier)
    (Mod.ihomAdjunction P.carrier)).symm (Mod.ihomMap f.hom.f)).app Q.carrier = _
  rw [Mod.ihomMap, Equiv.symm_apply_apply]

private instance tensorBifunctor_additive : (tensorBifunctor k₀ l X).Additive where
  map_add := by
    intro P P' f g
    apply NatTrans.ext
    funext Q
    apply Endofunctor.IsoAlgebra.hom_ext
    change (((tensorBifunctor k₀ l X).map (f + g)).app Q).hom.f =
      (((tensorBifunctor k₀ l X).map f).app Q).hom.f +
        (((tensorBifunctor k₀ l X).map g).app Q).hom.f
    simp only [tensorBifunctor_map]
    exact NatTrans.congr_app (Mod.tensorLeftMap_add f.hom.f g.hom.f) Q.carrier

private instance tensorBifunctor_obj_additive (P : ProEtaleWeilSheaf k₀ l X) :
    ((tensorBifunctor k₀ l X).obj P).Additive :=
  (tensorIhomAdjunction k₀ l X P).left_adjoint_additive

private def tensorBifunctorForget :
    Functor.uncurry.obj (tensorBifunctor k₀ l X) ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    change (((tensorBifunctor k₀ l X).map f.1).app P.2).hom.f ≫
        ((Mod.tensorLeft Q.1.carrier).map f.2.hom.f) = _
    rw [tensorBifunctor_map]
    rfl)

/-- The native underived tensor is additive, parameter-adjoint to the specified
native internal Hom, and its ordinary comparison is evaluation-normalized.

Source: the existing tensorIhomAdjunction and Stacks 06YS, 06YU;
step 2 of native tensor geometry.
(blueprint: lem-sf-native-weil-underived-tensor).

Proof: use the existing tensorFunctor in the variable being tensored. The maps
in its parameter are the mates of precomposition in ihomBifunctor. Mate functoriality
gives identity and composition and the parameter adjunction. Forgetting a mate is
the mate for Mod.ihomAdjunction, because both units and counits are the existing
underlying module maps. Mod.ihomMap is defined by that mate, so parameter maps forget
to Mod.tensorLeftMap. This proves additivity and makes the comparison the identity
on underlying objects. The formula for inverse adjunction is therefore the ordinary
uncurrying formula, with no scalar or sign. No derived category is constructed. -/
theorem native_weil_underived_tensor :
    ∃ T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X,
    ∃ _ : T.Additive, ∃ _ : ∀ P, (T.obj P).Additive,
    ∃ adj : T ⊣₂ ihomBifunctor k₀ l X,
    ∃ e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f := by
  refine ⟨tensorBifunctor k₀ l X, inferInstance, inferInstance,
    adjointBifunctorAdjunction (ihomBifunctor k₀ l X) (tensorFunctor k₀ l X)
      (tensorIhomAdjunction k₀ l X), tensorBifunctorForget k₀ l X, ?_⟩
  intro P Q I f
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
