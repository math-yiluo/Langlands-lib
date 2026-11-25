/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.TraceFormula.Main
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TraceSupertrace
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-!

# The trace on `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧` as a supertrace

For a separably closed field `Ω`, the categorical trace of an endomorphism `v` of a dualizable
object `P` of `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`, with the Koszul braiding, is the alternating sum of the
categorical traces of the induced endomorphisms `Hʲ(v)` of the homology sheaves `Hʲ(P)`
(blueprint `proposition-properties-trace`, item (4)). The two traces live in different rings: the
supertrace in `End (𝟙_ Mod_{Spec Ω})`, the trace in `End (𝟙_ Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧)`; they are
compared through the ring homomorphism `homologyUnitEndRingHom` placing an endomorphism of the
unit module in degree `0`.

## Main definitions

- `ProEtale.CondensedRing.homologyUnitEndRingHom`: `End (𝟙_ Mod_X) →+* End (𝟙_ Dᵇc(X)⟦Λ⟧)`.

## Main results

- `ProEtale.CondensedRing.trace_eq_homologyUnitEndRingHom_superTrace` (blueprint
  `proposition-properties-trace`, item (4)): every object of `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧` is a finite direct
  sum of shifts of the unit (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and on
  such objects of the ambient derived category the trace is the supertrace on homology
  (`DerivedCategory.trace_eq_singleFunctor_map_superTrace`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

-- The ring structure on the endomorphisms of the unit of `Dᵇc` takes long to synthesize.
/-- The endomorphisms of the unit module `Λ_X` act on the unit of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: an endomorphism
of `Λ_X` is placed in degree `0`. -/
noncomputable def homologyUnitEndRingHom :
    End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) →+* End (𝟙_
          (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  let F := HomologicalComplex.single
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
      (ComplexShape.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  have hι : Function.Bijective ((ObjectProperty.ι _).mapEndRingHom (𝟙_
      (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
  have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := CategoryTheory.Mod (Sheaf
      (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left)))) :=
    inferInstanceAs (IsIso (𝟙 _))
  ((RingEquiv.ofBijective _ hι).symm.toRingHom.comp
    ((asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := CategoryTheory.Mod (Sheaf
        (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
              X.left))))).symm.conjRingEquiv.toRingHom.comp
      (F.mapEndRingHom (CategoryTheory.Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left)))))

omit [IsSeparated X.hom] in
/-- Through the inclusion `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{Λ_X})`, `homologyUnitEndRingHom` is the placement
of endomorphisms of the unit in degree `0`, `DerivedCategory.singleFunctorUnitEndRingHom`. -/
lemma ι_map_homologyUnitEndRingHom
    (x : End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
        (homologyUnitEndRingHom ℓ X x).asHom =
      (DerivedCategory.singleFunctorUnitEndRingHom _ x).asHom := by
  unfold homologyUnitEndRingHom
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have hb : Function.Bijective ((ObjectProperty.ι (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))).mapEndRingHom (𝟙_
          (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
  refine (congrArg End.asHom ((RingEquiv.ofBijective _ hb).apply_symm_apply _)).trans ?_
  have hε : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left))) = 𝟙 _ :=
    rfl
  erw [RingHom.comp_apply]
  erw [Iso.conjRingEquiv_apply]
  simp only [Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv, hε, IsIso.inv_id]
  erw [Category.id_comp, Category.comp_id]
  rfl

attribute [local instance] boundedConstructibleBraiding in
/-- **The trace as a supertrace over a field** (blueprint `proposition-properties-trace`,
item (4)): for a separably closed field `Ω` and an endomorphism `v` of a dualizable object `P` of
`Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`, the categorical trace of `v` is the alternating sum
`∑ⱼ (-1)ʲ Tr(Hʲ(v) | Hʲ(P))` of the traces on the homology sheaves, placed in degree `0`.

The object `P` is a finite direct sum of shifts `𝟙⟦nⱼ⟧` of the unit
(`nonempty_shiftDecomposition_point`, through the fibre functor `Fib_s` of blueprint
`lemma-perfect-complexes-geometric-point`), and its homology sheaves are finite free, hence
dualizable. In the ambient derived category both sides are then sums over the summands, and on
`𝟙⟦n⟧` they are `(-1)ⁿ r` for the endomorphism `r` of the unit inducing the block
(`DerivedCategory.trace_eq_singleFunctor_map_superTrace`). -/
theorem trace_eq_homologyUnitEndRingHom_superTrace (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]
    (P : Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧) [HasRightDual P] (v : P ⟶ P) :
    trace v = (homologyUnitEndRingHom ℓ (point Ω)
      (superTrace
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).obj P.obj)
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).map v.hom))).asHom := by
  let A := PointMod ℓ Ω
  let I := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    (point Ω).left)).ι
  let := DerivedCategory.braidedCategory' A
  let : HasRightDual (I.obj P) :=
    @HasRightDual.mk _ _ _ _ (I.obj (Pᘁ)) (ExactPairing.map I P (Pᘁ))
  have hinj : Function.Injective I.unitEndRingHom := fun a b h ↦ by
    rw [Functor.unitEndRingHom_apply, Functor.unitEndRingHom_apply] at h
    apply End.ext
    have h := congrArg End.asHom h
    change 𝟙 _ ≫ I.map a.asHom ≫ 𝟙 _ = 𝟙 _ ≫ I.map b.asHom ≫ 𝟙 _ at h
    exact I.map_injective (by simpa only [Category.id_comp, Category.comp_id] using h)
  have hY (i : ℤ) : IsDualizable ((DerivedCategory.homologyFunctor A i).obj (I.obj P)) := by
    obtain ⟨n, ⟨e⟩⟩ := isFiniteFree_upperStar_homology ℓ (Field.toIsField Ω)
      IsField.isSepClosed_toField P i (𝟙 _)
    exact ⟨{ rightDual := _
             exact := (UnitBasis.ofIso (((upperStarId _ _).app _).symm ≪≫ e)).exactPairing }⟩
  suffices h : End.of (trace v) = homologyUnitEndRingHom ℓ (point Ω)
      (superTrace
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).obj P.obj)
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).map v.hom)) from
    congrArg End.asHom h
  apply hinj
  apply End.ext
  rw [← I.trace_eq_unitEndRingHom_trace v (I.map v) (Iso.refl _) (by simp),
    DerivedCategory.trace_eq_singleFunctor_map_superTrace
      ((nonempty_shiftDecomposition_point ℓ Ω P).some.map I) hY (I.map v),
    Functor.unitEndRingHom_apply, ι_map_homologyUnitEndRingHom]
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
