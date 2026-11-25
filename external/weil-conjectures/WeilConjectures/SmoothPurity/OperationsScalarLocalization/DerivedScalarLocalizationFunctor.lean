/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Unique additive localization of a linear functor

Extracted proved scalar-localization calculus used by the derived-operation construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open Opposite TensorProduct CategoryTheory
namespace WeilConjectures.OperationsScalarLocalization

/-- Unique additive localization of a linear functor.
Source: module base change (Stacks 00CV, 00CX), and the rational paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-localized-functor).
Proof: Use the semilinear extension with the identity coefficient homomorphism. Its coefficient
map is the identity by uniqueness. The extension has the stated object and pure-tensor formulas.
For uniqueness, use functor extensionality and induction on each tensor Hom group; additivity
handles zero and sums, and the prescribed formula handles pure tensors. -/
theorem functor_existsUnique
    {R : Type r} [CommRing R]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    (t : R) (U : C ⥤ D) [U.Additive] [U.Linear R] :
    ∃! F : ScalarLocalization R C t ⥤ ScalarLocalization R D t,
      F.Additive ∧ (∀ K, F.obj K = ⟨U.obj K.obj⟩) ∧
      (∀ (K L : C) (a : K ⟶ L) (c : Localization.Away t),
        HEq (F.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
          (c ⊗ₜ[R] U.map a)) := by
  have hsemi : ScalarLocalization.IsSemilinear (RingHom.id R) U := by
    intro K M c a
    exact U.map_smul c a
  let hu := IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)
  let J := ScalarLocalization.extension t t (RingHom.id R) hu U hsemi
  have hc : ScalarLocalization.coefficientMap t t (RingHom.id R) hu =
      RingHom.id (Localization.Away t) := by
    symm
    apply (ScalarLocalization.coefficientMap_unique t t (RingHom.id R) hu _).mp
    rfl
  have hJ (K M : C) (a : K ⟶ M)
      (c : Localization.Away t) :
      J.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M) =
        c ⊗ₜ[R] U.map a := by
    change ScalarLocalization.extensionHom t t (RingHom.id R) hu U hsemi K M
      (c ⊗ₜ[R] a) = _
    have h := Classical.choose_spec
      (ScalarLocalization.existsUnique_semilinearHom t t (RingHom.id R) hu U hsemi K M).exists
    unfold ScalarLocalization.extensionHom
    rw [h c a, hc]
    rfl
  refine ⟨J, ⟨inferInstance, fun _ ↦ rfl, fun K M a c ↦ heq_of_eq (hJ K M a c)⟩, ?_⟩
  intro J' hJ'
  have : J'.Additive := hJ'.1
  refine CategoryTheory.Functor.ext hJ'.2.1 ?_
  intro K M a
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
    apply (conj_eqToHom_iff_heq _ _ (hJ'.2.1 K) (hJ'.2.1 M)).2
    exact (hJ'.2.2 K.obj M.obj a c).trans (heq_of_eq (hJ K.obj M.obj a c).symm)
  | add a b ha hb =>
    rw [J'.map_add, J.map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) ha hb

end WeilConjectures.OperationsScalarLocalization
