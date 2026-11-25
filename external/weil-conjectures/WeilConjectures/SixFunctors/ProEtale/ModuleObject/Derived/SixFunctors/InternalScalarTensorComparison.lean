/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal

/-!
# The canonical scalar tensor comparison for internal modules

Source: blueprint main-20261015, proper-base-change-rational.proof.md (3), compatibility
of tensor with scalar extension; Stacks 07A4, tensor comparison for change of rings
(blueprint: def-sfb-internal-scalar-tensor-comparison).

The ordinary tensor comparison is specified by its universal property on scalar-unit
pairings. This property determines the entire strong monoidal structure uniquely. The
only postponed data construction uses that unique universal property, rather than an
unspecified isomorphism. The derived comparison is the existing bifunctor-derived lift.

## Main definitions and statements

- `InternalScalarMonoidalNormalized` and `internalScalarMonoidalNormalized_existsUnique`:
  the scalar-unit universal property and its uniqueness.
- `internalScalarMonoidal` and `internalScalar_preservesFlat`: the canonical ordinary
  monoidal structure and preservation of flat modules.
- `internalScalarExtension`: the existing total left derived scalar extension.
- `internalScalarTensorIso` and `internalScalarTensorComparison`: its canonical derived
  tensor isomorphism and underlying natural transformation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Reuse the sheaf and derived closed structures without expanding their constructions.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u})

/-- The universal scalar-unit normalization: the comonoidal map takes the unit of a
balanced tensor to the balanced tensor of the two scalar units.
Source: Stacks 07A4 and blueprint proper-base-change-rational.proof.md (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
def InternalScalarMonoidalNormalized
    (m : (Mod.extendScalars (coefficientMap a X)).Monoidal) : Prop :=
  ∀ M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X),
    Mod.tensorObjπ M N ≫ (Mod.extendUnit (coefficientMap a X) (M ⊗ N)).hom ≫
        (m.toOplaxMonoidal.δ M N).hom =
      ((Mod.extendUnit (coefficientMap a X) M).hom ⊗ₘ
        (Mod.extendUnit (coefficientMap a X) N).hom) ≫
          Mod.tensorObjπ ((Mod.extendScalars (coefficientMap a X)).obj M)
            ((Mod.extendScalars (coefficientMap a X)).obj N)

private lemma normalized_tensor_eq
    (m n : (Mod.extendScalars (coefficientMap a X)).Monoidal)
    (hm : InternalScalarMonoidalNormalized a X m)
    (hn : InternalScalarMonoidalNormalized a X n)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :
    m.toOplaxMonoidal.δ M N = n.toOplaxMonoidal.δ M N := by
  apply (Mod.extendHomEquiv (coefficientMap a X) (M ⊗ N) _).injective
  apply Mod.hom_ext
  change (Mod.extendUnit (coefficientMap a X) (M ⊗ N)).hom ≫
      (m.toOplaxMonoidal.δ M N).hom =
    (Mod.extendUnit (coefficientMap a X) (M ⊗ N)).hom ≫
      (n.toOplaxMonoidal.δ M N).hom
  exact (cancel_epi (Mod.tensorObjπ M N)).1 ((hm M N).trans (hn M N).symm)

private lemma normalized_unique
    (m n : (Mod.extendScalars (coefficientMap a X)).Monoidal)
    (hm : InternalScalarMonoidalNormalized a X m)
    (hn : InternalScalarMonoidalNormalized a X n) : m = n := by
  let F := Mod.extendScalars (coefficientMap a X)
  let := m
  have hδ := normalized_tensor_eq a X m n hm hn
  have h : m.toOplaxMonoidal.η ▷ F.obj (𝟙_ _) =
      n.toOplaxMonoidal.η ▷ F.obj (𝟙_ _) := by
    apply (cancel_epi (F.map (λ_ (𝟙_ _)).inv ≫ m.toOplaxMonoidal.δ (𝟙_ _) (𝟙_ _))).1
    simp only [Category.assoc]
    rw [← m.toOplaxMonoidal.oplax_left_unitality,
      hδ, ← n.toOplaxMonoidal.oplax_left_unitality]
  have hη : m.toOplaxMonoidal.η = n.toOplaxMonoidal.η := by
    have k := congrArg (fun f ↦ f ≫ (𝟙_ _) ◁ m.toOplaxMonoidal.η) h
    rw [← whisker_exchange, ← whisker_exchange] at k
    have k' := (cancel_epi (F.obj (𝟙_ _) ◁ m.toOplaxMonoidal.η)).1 k
    apply (cancel_epi (ρ_ (F.obj (𝟙_ _))).hom).1
    simpa only [rightUnitor_naturality] using
      congrArg (fun f ↦ f ≫ (ρ_ (𝟙_ _)).hom) k'
  apply Functor.Monoidal.toOplaxMonoidal_injective F
  apply Functor.OplaxMonoidal.ext
  · exact hη
  · funext M N
    exact hδ M N

/-- The scalar-unit universal property specifies one strong monoidal structure.
Source: Stacks 07A4, change of rings and total tensor; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison).
Proof: the balanced tensor universal property constructs
s tensor (m tensor n) ↦ (s tensor m) tensor (1 tensor n). The inverse multiplies the
scalar factors. Check both composites after the coequalizer coprojections; balancing
and the unit laws make them identities. Associativity and naturality follow on three
and two pure factors respectively. The regular module supplies the unit comparison.
S-linearity and generation by scalar-unit tensors determine the tensorator uniquely;
monoidal unitality then determines the unit map. Thus the whole structure is unique. -/
theorem internalScalarMonoidalNormalized_existsUnique :
    ∃! m : (Mod.extendScalars (coefficientMap a X)).Monoidal,
      InternalScalarMonoidalNormalized a X m := by
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal (coefficientMap a X)
  refine ⟨m, hm, ?_⟩
  intro n hn
  exact normalized_unique a X n m hn hm

/-- The strong monoidal structure selected by the unique scalar-unit universal property.
Source: Stacks 07A4; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
@[instance_reducible] def internalScalarMonoidal :
    (Mod.extendScalars (coefficientMap a X)).Monoidal :=
  (internalScalarMonoidalNormalized_existsUnique a X).exists.choose

/-- Extension of scalars preserves flat internal modules.
Source: Stacks 07A4, scalar tensor cancellation; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison).
Proof: tensoring an S-module with S tensor_R M, after restriction to R, is tensoring
that restricted module with M. The balanced tensor cancellation maps are inverse on
pure tensors. Restriction is exact and reflects exactness, so flatness of M gives
exactness of tensoring with its scalar extension. No flatness of S over R is used. -/
@[instance] theorem internalScalar_preservesFlat :
    (Mod.extendScalars (coefficientMap a X)).PreservesFlat := by
  exact Mod.extendScalars_preservesFlat (coefficientMap a X)

/- These structures agree through the recorded instances; their data need not unfold here. -/
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

variable [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

-- The general derived API carries graded tensor colimit instances.
/-- The total left derived extension of scalars, with its structural arguments shared
once for consumers. Its body is the existing generic total left derived functor.
Source: blueprint rational proof (3), coefficient change; Stacks 07A4
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
def internalScalarExtension :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj S X)) :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor

/-- The canonical scalar tensor comparison is an isomorphism, with the
bifunctor-derived normalization of the scalar-unit normalized ordinary tensorator.
Source: Stacks 07A4; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
def internalScalarTensorIso :
    (Functor.postcompose₂.obj (internalScalarExtension a X)).obj (derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (internalScalarExtension a X)).obj
        (internalScalarExtension a X)).obj (derivedTensor S X) :=
  letI := internalScalarMonoidal a X
  asIso (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison

/-- The canonical map T(A tensor_R B) → T(A) tensor_S T(B), constructed by the
bifunctor-derived lift of the scalar-unit normalized ordinary tensor comparison.
Source: Stacks 07A4 and blueprint proper-base-change-rational.proof.md (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
def internalScalarTensorComparison :
    (Functor.postcompose₂.obj (internalScalarExtension a X)).obj (derivedTensor R X) ⟶
      (((Functor.whiskeringLeft₂ _).obj (internalScalarExtension a X)).obj
        (internalScalarExtension a X)).obj (derivedTensor S X) :=
  (internalScalarTensorIso a X).hom

end AlgebraicGeometry.ProEtale.CondensedRing
