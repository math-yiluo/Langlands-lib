/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed

/-!

# Detection along finite jointly surjective families

Let `g_k : Z_k ⟶ X` be finitely many quasi-compact morphisms whose images cover `X`, for
instance the inclusions of the pieces of a decomposition of `X` into finitely many open and
closed subschemes. The pullbacks along the `g_k` jointly reflect isomorphisms: of module objects
over `Λ_X` (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_upperStar_of_cover`), of their
derived category
(`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover`) and of the
bounded constructible derived categories
(`ProEtale.CondensedRing.isIso_of_forall_isIso_boundedConstructibleUpperStar_map`). This is the
finite-family version of the open–closed detection of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed`, deduced in the same way
from the detection of zero morphisms of abelian sheaves
(`ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`).

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Cover

variable {X : Scheme.{u}} {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}} (g : ∀ k, Z k ⟶ X)
  [∀ k, QuasiCompact (g k)]

/-- A module object over `Λ_X` whose pullbacks along a finite quasi-compact jointly surjective
family vanish is zero. -/
theorem isZero_of_forall_isZero_upperStar (hg : ∀ x, ∃ k, x ∈ Set.range (g k).base)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∀ k, IsZero ((g k)^*⟦Λ⟧.obj M)) : IsZero M :=
  isZero_of_isZero_X Λ ((IsZero.iff_id_eq_zero _).2
    (ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g hg (𝟙 M.X) fun k ↦
      (((Mod.forget _).map_isZero (h k)).of_iso (upperStarObjXIso Λ (g k) M).symm).eq_of_src
        _ _))

/-- The pullbacks along a finite quasi-compact jointly surjective family jointly reflect
isomorphisms of module objects over `Λ_X`. -/
theorem jointlyReflectIsomorphisms_upperStar_of_cover
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k).base) :
    JointlyReflectIsomorphisms fun k ↦ (g k)^*⟦Λ⟧ where
  isIso {M N} φ h := by
    have hker (k : κ) : IsZero ((g k)^*⟦Λ⟧.obj (kernel φ)) :=
      (isZero_kernel_of_mono ((g k)^*⟦Λ⟧.map φ)).of_iso (PreservesKernel.iso _ φ)
    have hcoker (k : κ) : IsZero ((g k)^*⟦Λ⟧.obj (cokernel φ)) :=
      (isZero_cokernel_of_epi ((g k)^*⟦Λ⟧.map φ)).of_iso (PreservesCokernel.iso _ φ)
    have : Mono φ := Preadditive.mono_of_isZero_kernel _
      (isZero_of_forall_isZero_upperStar Λ g hg _ hker)
    have : Epi φ := Preadditive.epi_of_isZero_cokernel _
      (isZero_of_forall_isZero_upperStar Λ g hg _ hcoker)
    exact isIso_of_mono_of_epi φ

/-- The derived pullbacks along a finite quasi-compact jointly surjective family jointly reflect
isomorphisms of `D(Mod_{Λ_X})`. -/
theorem jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k).base) :
    JointlyReflectIsomorphisms fun k ↦ L((g k)^*⟦Λ⟧) :=
  (Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (jointlyReflectIsomorphisms_upperStar_of_cover Λ g hg)).of_iso
    fun k ↦ (leftDerivedUpperStarIsoMapDerivedCategory Λ (g k)).symm

end Cover

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ k in
/-- **Detection along a finite cover on bounded constructible complexes**: for finitely many
quasi-compact morphisms `g_k : Z_k ⟶ X` whose images cover `X`, a morphism `φ` of
`Dᵇc(X)⟦Λ⟧` such that every `Lg_k^* φ` is an isomorphism is an isomorphism. -/
theorem isIso_of_forall_isIso_boundedConstructibleUpperStar_map {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {κ : Type*} [Finite κ]
    {Z : κ → Over (Spec (.of k))} [∀ i, LocallyOfFiniteType (Z i).hom]
    [∀ i, QuasiCompact (Z i).hom] [∀ i, IsSeparated (Z i).hom] (g : ∀ i, Z i ⟶ X)
    [∀ i, QuasiCompact (g i).left] (hg : ∀ x, ∃ i, x ∈ Set.range (g i).left.base)
    {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K')
    (h : ∀ i, IsIso ((boundedConstructibleUpperStar Λ ℓ (g i)).map φ)) : IsIso φ := by
  have hι : IsIso ((boundedConstructible (condensedRingObj Λ X.left)).ι.map φ) :=
    ((jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover Λ (fun i ↦ (g i).left)
      hg).isIso_iff _).2 fun i ↦
      (NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility Λ ℓ (g i)) φ).1
        (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso φ (boundedConstructible (condensedRingObj Λ X.left)).ι

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
