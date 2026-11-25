/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointDerivedHom.PointDerivedHomModels
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.IntegralPointCoefficientAdjunction.IntegralPointCoefficientAdjunction
-- Reuse the proved tensor construction at independent site/coefficient universes.
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

set_option linter.privateModule false

/-! # Exact completed extension and sections at a point

Source: Stacks Project, Modules on Sites, Tags 03EI and 093M; blueprint
main-20261015, prose-10-04, proof, second sentence
(blueprint: lem-pod-point-exact-extension-sections).

The extension objects, their maps, local tensor generators and scalar-restricted
sections are the published PointDerivedHom constructions. Both the finite and integral
cases use arbitrary modules and sheaves. Cochain complexes may be unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

namespace WeilConjectures.PointDerivedHom

attribute [local instance 3000] abSheafify abLocallyBijective

variable (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)

private def constantPresheafHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (Q : PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R))) :
    ((constantPresheaf.{t, u} k R).obj M ⟶ Q) ≃
      (M ⟶ Q.obj (op (finalObject k))) where
  toFun f := f.app (op (finalObject k))
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        ((Q.map (toFinal k U.unop).op).hom.comp f.hom)
      naturality := by
        intro U V i
        ext x
        change Q.map (toFinal k V.unop).op (f.hom x) =
          Q.map i (Q.map (toFinal k U.unop).op (f.hom x))
        rw [← Q.map_comp_apply]
        have h : (toFinal k V.unop).op = (toFinal k U.unop).op ≫ i := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact (MorphismProperty.Over.w i.unop).symm
        rw [h] }
  left_inv f := by
    ext U x
    exact (PresheafOfModules.naturality_apply f (toFinal k U.unop).op x).symm
  right_inv f := by
    ext x
    change Q.map (toFinal k (finalObject k)).op (f.hom x) = f.hom x
    have h : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    rw [h, op_id, Q.map_id]
    rfl

private def constantHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (F : Modules.{t, u} k (constantRing.{t, u} k R)) :
    ((constantModules.{t, u} k R).obj M ⟶ F) ≃
      (M ⟶ (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) :=
  (PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t, max u (t + 1), t + 1}
    (constantUnit.{t, u} k R)).trans
    (constantPresheafHomEquiv.{t, u} k M
      ((PresheafOfModules.restrictScalars (constantUnit.{t, u} k R)).obj F.val))

private theorem constantHomEquiv_naturality_left
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N)
    (F : Modules.{t, u} k (constantRing.{t, u} k R))
    (g : (constantModules.{t, u} k R).obj N ⟶ F) :
    constantHomEquiv.{t, u} k M F ((constantModules.{t, u} k R).map f ≫ g) =
      f ≫ constantHomEquiv.{t, u} k N F g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
            (constantUnit.{t, u} k R)).map
          ((constantPresheaf.{t, u} k R).map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  rfl

private theorem constantHomEquiv_naturality_right
    (M : ModuleCat.{max u (t + 1)} R)
    {F G : Modules.{t, u} k (constantRing.{t, u} k R)}
    (f : (constantModules.{t, u} k R).obj M ⟶ F) (g : F ⟶ G) :
    constantHomEquiv.{t, u} k M G (f ≫ g) =
      constantHomEquiv.{t, u} k M F f ≫
        (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).map g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def constantAdjunction :
    constantModules.{t, u} k R ⊣
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantHomEquiv.{t, u} k
      homEquiv_naturality_left_symm := by
        intro M N F f g
        apply (constantHomEquiv.{t, u} k M F).injective
        rw [Equiv.apply_symm_apply, constantHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ constantHomEquiv_naturality_right k _ f g }

open SheafOfModules.CoefficientOrdinaryProof

private def extensionFunctor : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B :=
  constantModules.{t, u} k R ⋙ tensorFunctor.{max u (t + 1), t + 1, t} α

private def extensionSectionsIso :
    restriction.{max u (t + 1), t + 1, t} α ⋙ sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) ≅
      sections.{t, u} k B α :=
  NatIso.ofComponents (fun F ↦
    (show ((restriction.{max u (t + 1), t + 1, t} α ⋙
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) ≃ₗ[R]
      (sections.{t, u} k B α).obj F from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso) (by intros; rfl)

private def extensionAdjunction : extensionFunctor.{t, u} k B α ⊣ sections.{t, u} k B α :=
  ((constantAdjunction.{t, u} k).comp (tensorAdjunction.{max u (t + 1), t + 1, t} α)).ofNatIsoRight
    (extensionSectionsIso.{t, u} k B α)

private theorem constant_exact :
    PreservesFiniteLimits (constantModules.{t, u} k R) ∧
      PreservesFiniteColimits (constantModules.{t, u} k R) := by
  let P := constantPresheaf.{t, u} k R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P (PresheafOfModules.sheafification
    (constantUnit.{t, u} k R)),
    comp_preservesFiniteColimits P (PresheafOfModules.sheafification
      (constantUnit.{t, u} k R))⟩

end WeilConjectures.PointDerivedHom
