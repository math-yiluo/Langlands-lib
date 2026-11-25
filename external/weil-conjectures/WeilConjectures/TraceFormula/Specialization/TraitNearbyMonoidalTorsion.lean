/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveDevissage
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndSurjective
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStarBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# The nearby cycles of the trait are monoidal: finite field coefficients

Let `S = Spec k'⟦t⟧` be the strictly henselian trait of a separably closed field `k'`, with
geometric generic point `η̄ : Spec Ω ⟶ S`, and let `𝔽_E` be the residue field of the ring of
integers of a finite extension `E` of `ℚ_ℓ`. The nearby cycles of the trait are monoidal on
bounded constructible `𝔽̲_E`-complexes on `Spec Ω`: the Künneth map of the trait as a model of its
geometric generic point is an isomorphism
(`ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_residueField`),
in particular at the direct images `Rg_* K` of bounded constructible complexes along separated
morphisms of finite type `g : X ⟶ Spec Ω` (Deligne's finiteness theorem,
`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_residueField_lowerStar`).

## Proof

By `NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition` it suffices that
every bounded constructible complex `K` on the separably closed point `Spec Ω` is a finite direct
sum of shifts of the unit. This holds for every coefficient ring `Λ` whose regular module has
the endomorphisms of a field
(`ProEtale.CondensedRing.nonempty_shiftDecomposition_of_boundedConstructible_of_regular`), as
for `ℚ̄_ℓ` (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`):
* the endomorphisms of the unit of `Mod_{Spec Ω}` are those of the regular module `Λ`, through
  the equivalence with condensed `Λ`-modules, so every nonzero one is invertible;
* the cohomology sheaves `Hʲ(K)` are finitely presented
  (`ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject`), hence
  finite free (`CategoryTheory.Limits.exists_iso_biproduct_cokernel`);
* the unit is projective, `Spec Ω` being weakly contractible, so `K` is a shifted sum of finite
  free objects (`DerivedCategory.isShiftSum_of_isGE_of_isLE`), that is a finite direct sum of
  shifts of the unit.
For `Λ = 𝔽̲_E = C(-, 𝔽_E)` the global sections of the regular module are the constants `𝔽_E`
(`Profinite.continuousMapConstRingHom_surjective`), a field.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Finite direct sums of shifts -/

namespace CategoryTheory.ShiftDecomposition

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] {E P₁ P₂ : C} [HasBinaryBiproduct P₁ P₂]

/-- The decomposition of the binary biproduct `P₁ ⊞ P₂` obtained from decompositions of `P₁` and
`P₂`. -/
noncomputable def biprod (D₁ : ShiftDecomposition E P₁) (D₂ : ShiftDecomposition E P₂) :
    ShiftDecomposition E (P₁ ⊞ P₂) :=
  D₁.sum D₂ Limits.biprod.inl Limits.biprod.inr Limits.biprod.fst Limits.biprod.snd
    Limits.biprod.total Limits.biprod.inl_fst Limits.biprod.inr_snd Limits.biprod.inl_snd
    Limits.biprod.inr_fst

end CategoryTheory.ShiftDecomposition

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] {R : ObjectProperty C}

/-- A shifted sum of objects `X` satisfying `R` is a finite direct sum of shifts of `E`, if every
such `X[0]` is. -/
lemma IsShiftSum.nonempty_shiftDecomposition {M : DerivedCategory C} (hM : IsShiftSum R M)
    (E : DerivedCategory C)
    (hR : ∀ X, R X → Nonempty (ShiftDecomposition E ((singleFunctor C 0).obj X))) :
    Nonempty (ShiftDecomposition E M) := by
  let Q : ObjectProperty (DerivedCategory C) := fun P ↦ Nonempty (ShiftDecomposition E P)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e ⟨D⟩ ↦ ⟨D.ofIso e⟩⟩
  exact hM.prop Q (fun _ hX ↦ ⟨.ofIsZero hX⟩) (fun _ _ ⟨DX⟩ ⟨DY⟩ ↦ ⟨DX.biprod DY⟩)
    (fun _ n ⟨D⟩ ↦ ⟨D.shift n⟩) hR

end DerivedCategory

/-! ### The regular module of a field of constants -/

namespace Profinite

variable (T : Type) [TopologicalSpace T] [Field T] [IsTopologicalRing T]

/-- Every nonzero endomorphism of the regular module `C(-, T)` over a topological field `T` is
invertible: the endomorphisms are the multiplications by the constants `T`. -/
theorem isIso_of_ne_zero_end_regular_continuousMapRingObj
    (t : End (Mod.regular (continuousMapRingObj.{u} T))) (ht : t ≠ 0) : IsIso t.asHom :=
  isIso_of_ne_zero_of_surjective (Mod.regularEndRingHom.comp (continuousMapConstRingHom T))
    (Mod.regularEndRingHom_surjective.comp (continuousMapConstRingHom_surjective T)) t ht

end Profinite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Bounded constructible complexes on a separably closed point -/

section Point

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Ω : Type u} [CommRing Ω]

/-- If every nonzero endomorphism of the regular module `Λ` is invertible, so is every nonzero
endomorphism of the unit of `Mod_{Spec Ω}` for a separably closed field `Ω`: the pullback from the
point is an equivalence with condensed `Λ`-modules. -/
theorem isIso_of_ne_zero_end_tensorUnit_of_regular
    (hΛ : ∀ t : End (Mod.regular Λ), t ≠ 0 → IsIso t.asHom) (hΩ : IsField Ω)
    (hsep : letI := hΩ.toField; IsSepClosed Ω)
    (t : End (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))))) (ht : t ≠ 0) :
    IsIso t.asHom := by
  let := hΩ.toField
  have := isEquivalence_upperStarFromPointMod (Ω := Ω) Λ
  exact (upperStarFromPointMod _ _).isIso_of_ne_zero_end (Iso.refl _) hΛ t ht

/-- If every nonzero endomorphism of the regular module `Λ` is invertible, the cohomology sheaves
of a bounded constructible complex on a separably closed point `Spec Ω` are finite free: they are
finitely presented, and the endomorphisms of the unit form a field. -/
theorem isFree_homology_of_boundedConstructible
    (hΛ : ∀ t : End (Mod.regular Λ), t ≠ 0 → IsIso t.asHom) (hΩ : IsField Ω)
    (hsep : letI := hΩ.toField; IsSepClosed Ω)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω))))}
    (hK : boundedConstructible (condensedRingObj Λ (Spec (.of Ω))) K) (j : ℤ) :
    Mod.IsFree (condensedRingObj Λ (Spec (.of Ω)))
      ((DerivedCategory.homologyFunctor _ j).obj K) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := isFinitelyPresented_upperStar_of_isConstructibleModuleObject Λ hΩ hsep
    (((mem_boundedConstructible_iff _ _).1 hK).2 j) (𝟙 _)
  obtain ⟨k, ⟨e'⟩⟩ := Limits.exists_iso_biproduct_cokernel
    (isIso_of_ne_zero_end_tensorUnit_of_regular Λ hΛ hΩ hsep) (Iso.refl _) (Iso.refl _) f
  exact ⟨k, ⟨((upperStarId _ _).app _).symm ≪≫ e ≪≫ e'⟩⟩

/-- **Bounded constructible complexes on a separably closed point split**: if every nonzero
endomorphism of the regular module `Λ` is invertible, every bounded constructible complex on a
separably closed point `Spec Ω` is a finite direct sum of shifts of the unit. Its cohomology
sheaves are finite free, hence projective, so the truncation triangles split. -/
theorem nonempty_shiftDecomposition_of_boundedConstructible_of_regular
    (hΛ : ∀ t : End (Mod.regular Λ), t ≠ 0 → IsIso t.asHom) (hΩ : IsField Ω)
    (hsep : letI := hΩ.toField; IsSepClosed Ω)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω))))}
    (hK : boundedConstructible (condensedRingObj Λ (Spec (.of Ω))) K) :
    Nonempty (ShiftDecomposition (𝟙_ _) K) := by
  have hH := isFree_homology_of_boundedConstructible Λ hΛ hΩ hsep hK
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := hK
  let := hΩ.toField
  have : Projective (Mod.regular (condensedRingObj Λ (Spec (.of Ω)))) :=
    projective_regular_of_isSepClosed (k := Ω) _
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (Mod.IsFree (condensedRingObj Λ (Spec (.of Ω)))) :=
    ⟨fun e ⟨n, ⟨e'⟩⟩ ↦ ⟨n, ⟨e.symm ≪≫ e'⟩⟩⟩
  refine (DerivedCategory.isShiftSum_of_isGE_of_isLE (R := Mod.IsFree _)
    (fun _ hX ↦ ⟨0, ⟨hX.iso (isZero_biproduct_fin_zero _)⟩⟩)
    (fun _ ⟨n, ⟨e⟩⟩ ↦ Projective.of_iso e.symm (Mod.projective_finiteFree n)) ha hb
    hH).nonempty_shiftDecomposition _ ?_
  rintro X ⟨n, ⟨e⟩⟩
  let S := DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω)))
    Ab.{u + 1}) (condensedRingObj Λ (Spec (.of Ω)))) 0
  let Q : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))) := fun X ↦
    Nonempty (ShiftDecomposition (𝟙_ _) (S.obj X))
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e ⟨D⟩ ↦ ⟨D.ofIso (S.mapIso e)⟩⟩
  have := preservesBinaryBiproducts_of_preservesBiproducts S
  exact Q.prop_of_iso e.symm (Q.prop_biproduct_fin (fun _ hX ↦ ⟨.ofIsZero (S.map_isZero hX)⟩)
    (fun X Y ⟨DX⟩ ⟨DY⟩ ↦ ⟨(DX.biprod DY).ofIso (S.mapBiprod X Y).symm⟩)
    ⟨(ShiftDecomposition.self _).ofIso (DerivedCategory.singleFunctorObjUnitIso _).symm⟩ n)

end Point

/-! ### Finite field coefficients -/

section ResidueField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- Over a separably closed field `Ω`, every bounded constructible `𝔽̲_E`-complex on `Spec Ω` is a
finite direct sum of shifts of the unit. -/
theorem nonempty_shiftDecomposition_residueField {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
        (Spec (.of Ω))))}
    (hK : boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E)) (Spec (.of Ω))) K) :
    Nonempty (ShiftDecomposition (𝟙_ _) K) :=
  nonempty_shiftDecomposition_of_boundedConstructible_of_regular _
    (Profinite.isIso_of_ne_zero_end_regular_continuousMapRingObj _) (Field.toIsField Ω)
    IsField.isSepClosed_toField hK

namespace NearbyCyclesModel

variable (k' : Type u) [Field k'] [IsSepClosed k']

/-- **The nearby cycles of the trait are monoidal on the geometric generic point, with
coefficients `𝔽_E`**: the Künneth map of the trait `T` (as a model of its geometric generic point
`Spec Ω`) with coefficients `𝔽̲_E` is an isomorphism at `(C, D)` for every bounded constructible
`C`, which is a finite direct sum of shifts of the unit. -/
theorem isIso_kunnethMap_traitGenericModel_residueField
    (C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (traitGenericModel k').generic)
      Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
        (traitGenericModel k').generic)))
    (hC : boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
        (traitGenericModel k').generic) C) :
    IsIso (kunnethMap (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
      (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k')) C D) :=
  isIso_kunnethMap_traitGenericModel_of_shiftDecomposition _ k' C D
    (nonempty_shiftDecomposition_residueField ℓ E (Ω := traitGenericField k') hC)

end NearbyCyclesModel

end ResidueField

section ResidueFieldLowerStar

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

namespace NearbyCyclesModel

variable (k' : Type u) [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

/-- **The Künneth map of the trait at direct images, with coefficients `𝔽_E`**: for a separated
morphism of finite type `g : X ⟶ Spec Ω` to the geometric generic point of the trait and a
bounded constructible `𝔽̲_E`-complex `K` on `X`, the Künneth map of the trait `T` is an
isomorphism at `(Rg_* K, D)`: `Rg_* K` is bounded constructible (Deligne's finiteness theorem,
`ℓ` being invertible on `Spec Ω`). -/
theorem isIso_kunnethMap_traitGenericModel_residueField_lowerStar {X : Scheme.{u}}
    (g : X ⟶ Spec (.of (traitGenericField k'))) [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E)) X))}
    (hK : boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E)) X) K)
    (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (traitGenericModel k').generic)
      Ab.{u + 1}) (condensedRingObj
        (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
        (traitGenericModel k').generic))) :
    IsIso (kunnethMap (Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E))
      (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k'))
      (R((g)_*⟦Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E)⟧).obj K)
      D) := by
  have hℓ : ((ℓ : ℕ) : traitGenericField k') ≠ 0 := by
    intro h
    rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec _ ℓ).1 h) with h₁ | h₁
    · exact CharP.ringChar_ne_one h₁
    · exact (Fact.out : ringChar (traitGenericField k') ≠ ℓ) h₁
  exact isIso_kunnethMap_traitGenericModel_residueField ℓ E k' _ D
    (boundedConstructible_rightDerivedLowerStar_obj_of_finite _ ℓ hℓ
      (PadicAlgCl.natCast_eq_zero_integersResidueField ℓ E) (𝟙 _) g hK)

end NearbyCyclesModel

end ResidueFieldLowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
