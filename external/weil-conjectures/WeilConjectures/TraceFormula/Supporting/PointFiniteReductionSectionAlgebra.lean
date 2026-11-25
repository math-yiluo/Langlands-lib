/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.PointSectionsFiniteReductionData
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-! # Ordinary finite quotient sections and flatness

Source: Stacks Tags 093J, 03EK and 00HD; steps 2--3 of
`lem-trf-point-sections-finite-reduction`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

private theorem constantSection_bijective (k A : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] : Function.Bijective (pointConstantSectionMap k A) := by
  exact AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _)
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))

private def constantSectionEquiv (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] :=
  RingEquiv.ofBijective (pointConstantSectionMap k A) (constantSection_bijective k A)

private def sheafificationFinalIso (k : Type u) [Field k] [IsAlgClosed k]
    (R : Sheaf (ProEt.topology (Spec (.of k))) RingCat.{u + 1})
    (P : PresheafOfModules.{u + 1} R.obj) :
    P.obj (op (ProEt.mk (𝟙 (Spec (.of k))))) ≅
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of k))))) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P
  let φ : P.obj U ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj U :=
    ModuleCat.ofHom (X := P.obj U)
      (Y := ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val.obj U)
      { toFun := fun x ↦ η.app U x
        map_add' := fun x y ↦ (η.app U).hom.map_add x y
        map_smul' := fun a x ↦ (η.app U).hom.map_smul a x }
  have hφ : Function.Bijective φ :=
    AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso (Iso.refl _) P.presheaf
  exact (LinearEquiv.ofBijective φ.hom hφ).toModuleIso


end WeilConjectures
