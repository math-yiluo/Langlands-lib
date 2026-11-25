/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionIsIso
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionShift
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Restricting a refinement to its distinguished open component -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- The inverse-transpose word for a specified invertible restriction.
Source: adjunction unit and counit identities
(blueprint: lem-sf-refinement-open-restriction). -/
@[irreducible] def normalizedOpenAdjunct
    {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (a : J ⊣ U) (H : A ⥤ B) (V : A ⥤ A)
    (η : 𝟭 A ⟶ V) (θ : H ⋙ U ⟶ V) [IsIso θ] : J ⟶ H :=
  J.leftUnitor.inv ≫ Functor.whiskerRight (η ≫ inv θ) J ≫
    (Functor.associator H U J).hom ≫ Functor.whiskerLeft H a.counit ≫ H.rightUnitor.hom

private theorem normalizedOpenAdjunct_normalization
    {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (a : J ⊣ U) (H : A ⥤ B) (V : A ⥤ A)
    (η : 𝟭 A ⟶ V) (θ : H ⋙ U ⟶ V) [IsIso θ] (M : A)
    (σ : (H ⋙ U).obj M ⟶ V.obj M) (hσ : θ.app M = σ) :
    a.homEquiv M (H.obj M) ((normalizedOpenAdjunct a H V η θ).app M) ≫ σ =
      η.app M := by
  subst σ
  have he : (normalizedOpenAdjunct a H V η θ).app M =
      (a.homEquiv M (H.obj M)).symm (η.app M ≫ (inv θ).app M) := by
    simp [normalizedOpenAdjunct, Adjunction.homEquiv_counit, Category.assoc]
  rw [he, Equiv.apply_symm_apply, Category.assoc, ← NatTrans.comp_app, IsIso.inv_hom_id]
  simp

private theorem normalizedOpenAdjunct_shift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {J : A ⥤ B} {U : B ⥤ A} [J.CommShift ℤ] [U.CommShift ℤ]
    (a : J ⊣ U) [a.CommShift ℤ] (H : A ⥤ B) (V : A ⥤ A)
    [H.CommShift ℤ] [V.CommShift ℤ]
    (η : 𝟭 A ⟶ V) (θ : H ⋙ U ⟶ V) [IsIso θ]
    [η.CommShift ℤ] [θ.CommShift ℤ] :
    (normalizedOpenAdjunct a H V η θ).CommShift ℤ := by
  let := NatTrans.CommShift.of_isIso θ ℤ
  rw [normalizedOpenAdjunct]
  infer_instance

end CategoryTheory

namespace WeilConjectures.PurCompactSupport

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction openDerivedAdjunction refinementRestriction

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/-- The canonical restriction is a shift-compatible isomorphism.
Source: Stacks 0F7B and 0F7I, restriction to the distinguished clopen section.
(blueprint: lem-sf-refinement-open-restriction).

Proof: form V = c.Z ×[d.Z] X. The section induced by c.i is open because c.i is
open, and closed because r is separated. Open restriction commutes with derived
direct image: its exact left adjoint implies preservation of K-injectives, and the
underived exchange is the sectionwise pullback identification. Pulling c.i-extension
by zero to V gives extension from this clopen section. Clopen extension is exact
direct image, and its composite with V → X is identity direct image. Under these
identifications the proper counit is restriction to the distinguished component,
so the displayed restriction map is invertible. Naturality is that of the pullback
compositor and counit. The exact open pullback compositor and the canonical derived
proper adjunction commute with integer shifts; their composite does too. This proves
the shift equation for the actual specified components, not for unrelated objectwise
choices. It works for arbitrary compatible coefficient sheaves and unbounded
complexes. Empty sections give zero objects and identity refinements give the open
unit identification. The component condition determines the transformation uniquely. -/
theorem exists_refinementRestriction :
    ∃ θ : ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
        (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i,
      (∀ M, θ.app M = refinementRestriction R r hi M) ∧
        IsIso θ ∧ θ.CommShift ℤ := by
  obtain ⟨θ, hθ⟩ := refinementRestriction_data R r hi
  exact ⟨θ, hθ, refinementRestriction_data_isIso R r hi θ hθ,
    refinementRestriction_data_shift R r hi θ hθ⟩

/-- Naturality of the specified restriction components.
Source: the normalized restriction calculation, Stacks 0F7B
(blueprint: lem-sf-refinement-open-restriction). -/
theorem refinementRestriction_naturality
    {M N : DerivedCategory (pbcModules X (R.ring X))} (a : M ⟶ N) :
    (((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i).map a ≫
        refinementRestriction R r hi N =
      refinementRestriction R r hi M ≫
        ((openExtension R c.i).mapDerivedCategory ⋙ pull R c.i).map a := by
  obtain ⟨θ, happ, _, _⟩ := exists_refinementRestriction R r hi
  rw [← happ M, ← happ N]
  exact θ.naturality a

/-- The restriction transformation with its literal, specified components.
Source: Stacks 0F7B, the proper counit restriction
(blueprint: lem-sf-refinement-open-restriction). -/
@[irreducible] def refinementRestrictionNat :
    ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
      (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i where
  app M := refinementRestriction R r hi M
  naturality {_M _N} a := refinementRestriction_naturality R r hi a

private theorem refinementRestrictionNat_app
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    (refinementRestrictionNat R r hi).app M = refinementRestriction R r hi M := by
  rw [refinementRestrictionNat]

/-- The restriction transformation is invertible.
Source: the normalized restriction calculation, Stacks 0F7B
(blueprint: lem-sf-refinement-open-restriction). -/
theorem refinementRestrictionNat_isIso : IsIso (refinementRestrictionNat R r hi) := by
  obtain ⟨θ, happ, hiso, _⟩ := exists_refinementRestriction R r hi
  have he : refinementRestrictionNat R r hi = θ := by
    ext M
    rw [refinementRestrictionNat_app, happ M]
  rw [he]
  exact hiso

attribute [local instance] refinementRestrictionNat_isIso

/-- The restriction transformation has its canonical cochain shifts.
Source: exact pullback composition and the derived counit, Stacks 0F7B
(blueprint: lem-sf-refinement-open-restriction). -/
theorem refinementRestrictionNat_shift :
    (refinementRestrictionNat R r hi).CommShift ℤ := by
  obtain ⟨θ, happ, _, hshift⟩ := exists_refinementRestriction R r hi
  have he : refinementRestrictionNat R r hi = θ := by
    ext M
    rw [refinementRestrictionNat_app, happ M]
  rw [he]
  exact hshift

/-- The adjunct of the inverse restriction applied to the open unit. Its construction
is on the ambient derived category; invertibility will require the finite-Tor domain.
Source: Stacks 0F7B and 0F7I
(blueprint: lem-sf-refinement-open-restriction). -/
@[irreducible] def refinementOpenMap :
    (openExtension R d.i).mapDerivedCategory ⟶
      (openExtension R c.i).mapDerivedCategory ⋙ push R r.hom :=
  normalizedOpenAdjunct (openDerivedAdjunction R d.i)
    ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom)
    ((openExtension R c.i).mapDerivedCategory ⋙ pull R c.i)
    (openDerivedAdjunction R c.i).unit (refinementRestrictionNat R r hi)

/-- The constructed open map has exactly the specified transpose.
Source: adjunction triangle identities, Stacks 0F7I
(blueprint: lem-sf-refinement-open-restriction). -/
theorem refinementOpenMap_normalization (M : DerivedCategory (pbcModules X (R.ring X))) :
    (openDerivedAdjunction R d.i).homEquiv _ _ ((refinementOpenMap R r hi).app M) ≫
        refinementRestriction R r hi M = (openDerivedAdjunction R c.i).unit.app M := by
  rw [refinementOpenMap]
  exact CategoryTheory.normalizedOpenAdjunct_normalization
    (J := (openExtension R d.i).mapDerivedCategory) (U := pull R d.i)
    (openDerivedAdjunction R d.i)
    ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom)
    ((openExtension R c.i).mapDerivedCategory ⋙ pull R c.i)
    (openDerivedAdjunction R c.i).unit (refinementRestrictionNat R r hi) M
    (refinementRestriction R r hi M) (refinementRestrictionNat_app R r hi M)

private theorem openAdjunction_shift {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] : (openDerivedAdjunction R j).CommShift ℤ := by
  unfold openDerivedAdjunction
  apply Adjunction.CommShift.mk'
  exact ((openAdjunction R j).mapExactDerivedCategory_unit_commShift).2

private theorem pullAdjunction_shift {U V : Scheme.{u}} (g : U ⟶ V) :
    (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).CommShift ℤ := by
  unfold proEtaleRingDerivedAdjunction
  exact canonicalRightDerivedAdjunctionShift
    (proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g))

/-- The normalized pullback compositor has its usual cochain shift structure.
Source: exact-functor localization, Stacks 0D6D
(blueprint: lem-sf-refinement-open-restriction). -/
theorem geometricPullComposition_shift {U V W : Scheme.{u}}
    (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    (geometricPullComposition R h k hc).hom.CommShift ℤ := by
  dsimp only [geometricPullComposition, Iso.trans_hom]
  infer_instance

/-- Proper composition has the conjugate cochain shifts.
Source: mates of shift-compatible transformations, Stacks 0D6D
(blueprint: lem-sf-refinement-open-restriction). -/
theorem geometricPushComposition_shift {U V W : Scheme.{u}}
    (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    (geometricPushComposition R h k hc).hom.CommShift ℤ := by
  let := pullAdjunction_shift R h
  let := pullAdjunction_shift R k
  let := pullAdjunction_shift R (h ≫ k)
  let := geometricPullComposition_shift R h k hc
  change (conjugateEquiv _ _ (geometricPullComposition R h k hc).hom).CommShift ℤ
  infer_instance

/-- The inverse-transpose construction respects ordinary integer shifts.
Source: exact open units and counits and the proper counit, Stacks 0F7B
(blueprint: lem-sf-refinement-open-restriction). -/
theorem refinementOpenMap_shift : (refinementOpenMap R r hi).CommShift ℤ := by
  let := openAdjunction_shift R c.i
  let := openAdjunction_shift R d.i
  let := refinementRestrictionNat_shift R r hi
  rw [refinementOpenMap]
  apply CategoryTheory.normalizedOpenAdjunct_shift

end WeilConjectures.PurCompactSupport
