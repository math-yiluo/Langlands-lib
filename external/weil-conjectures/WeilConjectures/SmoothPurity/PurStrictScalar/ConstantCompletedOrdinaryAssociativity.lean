/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitReduction

/-! # Ordinary constant-to-completed scalar associativity

Source: Stacks 03EK and 07A6. Successive adjunction transposes reduce the
associativity square to the tensor units.
(blueprint: lem-pur-constant-completed-ordinary-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar

/-- The ordinary associator fixed by tensor-unit normalized adjunctions.
Source: Stacks 03EK, 07A6
(blueprint: def-pur-ordinary-scalar-associator). -/
def ordinaryScalarAssociator {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d) :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend d :=
  (((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).ofNatIsoRight
    (pbcRestrictComp a b d h)).leftAdjointUniq (pbcScalarAdjunction d)

private theorem homEquiv_section {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (N : pbcModules W S) (f : (pbcExtend a).obj M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction a).homEquiv M N f).val.app U x =
      f.val.app U (pbcTensorSection a M U 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change f.val.app U (((pbcScalarAdjunction a).unit.app M).val.app U x) = _
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec]

private theorem tensor_map_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcExtend a).map f).val.app U (pbcTensorSection a M U 1 x) =
      pbcTensorSection a N U 1 (f.val.app U x) := by
  have h := (pbcScalarAdjunction a).unit.naturality f
  have h' := congrArg (fun g ↦ g.val.app U x) h
  change (((pbcScalarAdjunction a).unit.app N).val.app U (f.val.app U x)) =
    ((pbcExtend a).map f).val.app U
      (((pbcScalarAdjunction a).unit.app M).val.app U x) at h'
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec,
    (pbcScalarAdjunction_exists a).exists.choose_spec] at h'
  exact h'.symm

private theorem associator_unit {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryScalarAssociator a b d h).hom.app M).val.app U
      (pbcTensorSection b ((pbcExtend a).obj M) U 1
        (pbcTensorSection a M U 1 x)) = pbcTensorSection d M U 1 x := by
  let ad := ((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).ofNatIsoRight
    (pbcRestrictComp a b d h)
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app ad (pbcScalarAdjunction d) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
  have hz := congrArg (fun f ↦ f.val.app U x) hh
  change ((pbcRestrictComp a b d h).hom.app ((pbcExtend d).obj M)).val.app U
    ((((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).homEquiv M _
      ((ordinaryScalarAssociator a b d h).hom.app M)).val.app U x) = _ at hz
  erw [(pbcRestrictComp_exists a b d h).exists.choose_spec] at hz
  change ((pbcScalarAdjunction a).homEquiv M _
    ((pbcScalarAdjunction b).homEquiv _ _
      ((ordinaryScalarAssociator a b d h).hom.app M))).val.app U x = _ at hz
  erw [homEquiv_section, homEquiv_section,
    (pbcScalarAdjunction_exists d).exists.choose_spec] at hz
  exact hz

private theorem successive_unit_ext {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (M : pbcModules W R) (N : pbcModules W T)
    (f g : (pbcExtend b).obj ((pbcExtend a).obj M) ⟶ N)
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (pbcTensorSection b ((pbcExtend a).obj M) U 1
        (pbcTensorSection a M U 1 x)) =
      g.val.app U (pbcTensorSection b ((pbcExtend a).obj M) U 1
        (pbcTensorSection a M U 1 x))) : f = g := by
  apply ((pbcScalarAdjunction b).homEquiv _ _).injective
  apply ((pbcScalarAdjunction a).homEquiv _ _).injective
  ext U x
  erw [homEquiv_section, homEquiv_section, homEquiv_section, homEquiv_section]
  exact h U x

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u})

attribute [local irreducible] ordinaryScalarAssociator scalarCompletionOrdinary
  reductionChange completedAdicChange

end WeilConjectures.PurStrictScalar
