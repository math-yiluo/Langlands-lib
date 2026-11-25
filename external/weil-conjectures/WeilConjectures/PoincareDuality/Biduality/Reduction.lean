/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.PoincareDuality.Biduality.ReductionIhom

/-!
# Biduality along the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`

Write `R = (𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})` for the reduction modulo
`ℓⁿ` of bounded constructible `𝒪_E`-complexes, with values in the ambient derived category of
module objects over `(𝒪_E ⧸ ℓⁿ)_X`. This file proves the integral step (ii) of blueprint
`theorem-verdier-biduality`: `R` is lax braided monoidal and commutes with internal homs, so it
carries the double-dual morphism `δ_{K₀}` of `K₀` (relative to `ω_{X, 𝒪_E}`) to the double-dual
morphism of `R K₀` (relative to `R ω_{X, 𝒪_E}`), and `R` detects isomorphisms (derived Nakayama).

## Main results

- `ProEtale.CondensedRing.isIso_of_isIso_integersModPowReductionAmbient_map`: derived Nakayama, a
  morphism of bounded constructible `𝒪_E`-complexes whose reduction modulo `ℓⁿ` (`n ≠ 0`) is an
  isomorphism is an isomorphism.
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_isIso_toIhomIhom_reduction`: `δ_{K₀}` is an
  isomorphism as soon as the double-dual morphism of `R K₀` relative to `R ω_{X, 𝒪_E}` is.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.ObjectProperty

open Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  [Category* D] [MonoidalCategory D] [MonoidalClosed D]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed]

/-- The comparison maps `ι [A, B] ⟶ [ι A, ι B]` of the inclusion of a full monoidal closed
subcategory are identities. -/
lemma ihomComparison_ι_app (A B : P.FullSubcategory) :
    (ihomComparison P.ι A).app B = 𝟙 ((ihom A.obj).obj B.obj) := by
  apply uncurry_injective
  rw [ihomComparison_app_eq_curry, uncurry_curry]
  exact (Category.id_comp _).trans (uncurry_id_eq_ev _ _).symm

/-- The comparison maps of the restriction `P.ι ⋙ F` of a lax monoidal functor `F` to a full
monoidal closed subcategory are those of `F`. -/
lemma ihomComparison_ι_comp_app (F : C ⥤ D) [F.LaxMonoidal] (A B : P.FullSubcategory) :
    (ihomComparison (P.ι ⋙ F) A).app B =
      (ihomComparison F A.obj).app B.obj := by
  rw [ihomComparison_comp_app, ihomComparison_ι_app]
  exact (congrArg (· ≫ _) (F.map_id _)).trans (Category.id_comp _)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The reduction modulo `ℓⁿ` of bounded constructible `𝒪_E`-complexes, with values in the
ambient derived category of module objects over `(𝒪_E ⧸ ℓⁿ)_X`: the inclusion followed by the
derived extension of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`. -/
noncomputable abbrev integersModPowReductionAmbient :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 n) X.left)) :=
  (boundedConstructible _).ι ⋙ L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n))

/-- The derived reduction modulo `ℓⁿ`, `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤
D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})`, is monoidal, with comonoidal structure the tensor comparison
`Functor.leftDerivedTensorComparison`. -/
@[instance_reducible]
noncomputable def leftDerivedIntegersModPowReductionMonoidal :
    L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).Monoidal :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction X.left ℓ E.1 n)
  (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctorMonoidal

attribute [local instance] leftDerivedIntegersModPowReductionMonoidal

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- Blueprint
`proposition-six-operations-change-coefficients`, (2), for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`. **Reduction modulo `ℓⁿ` commutes with internal homs**: for bounded constructible
`𝒪_E`-complexes `A` and `B`, the comparison
`v_{A,B} : RHom(A, B) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ RHom(A ⊗ᴸ 𝒪_E ⧸ ℓⁿ, B ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`, the transpose of the
reduction of the evaluation (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), is an
isomorphism: the restriction to bounded constructible complexes of
`ProEtale.CondensedRing.isIso_ihomComparison_leftDerivedIntegersModPowReduction` (blueprint
`proposition-six-operations-change-coefficients--7`). -/
theorem isIso_ihomComparison_integersModPowReduction
    (A B : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso ((Functor.LaxMonoidal.ihomComparison
      L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)) A.obj).app B.obj) :=
  isIso_ihomComparison_leftDerivedIntegersModPowReduction_of_eq ℓ E.1 n X.left
    (leftDerivedIntegersModPowReductionMonoidal ℓ E n X) rfl A.obj B.obj

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated X.hom] in
/-- **Reduction modulo `ℓⁿ` detects zero objects** (`n ≠ 0`): a bounded constructible
`𝒪_E`-complex `K` whose reduction `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ` vanishes is zero. By the reduction triangle
`ℓⁿ` acts invertibly on `K`, hence on its first derived reduction, where `ℓ` acts by zero; so the
first derived reduction vanishes and `K = 0` by derived Nakayama (blueprint
`lemma-reduction-derived-nakayama`). This is the argument of
`ProEtale.CondensedRing.isZero_of_isZero_etaleReduction`. -/
theorem isZero_of_isZero_integersModPowReductionAmbient_obj (hn : n ≠ 0)
    {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    (h : Limits.IsZero ((integersModPowReductionAmbient ℓ E n X).obj K)) : Limits.IsZero K := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  -- by the reduction triangle, `ℓⁿ` acts invertibly on `K`
  obtain ⟨g, δ, hT⟩ := exists_distinguished_integersModPowReduction X.left ℓ E.1 n K.obj
  have hK : IsIso ((ℓ : ℤ) ^ n • 𝟙 K.obj) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 (Functor.map_isZero _ h)
  -- hence `K = 0` by derived Nakayama
  exact isZero_of_isIso_pow_zsmul_id X.left ℓ E.1 hn hK

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated X.hom] in
/-- **Derived Nakayama for the reduction modulo `ℓⁿ`** (blueprint
`lemma-reduction-derived-nakayama`): for `n ≠ 0`, a morphism `f` of bounded constructible
`𝒪_E`-complexes whose reduction modulo `ℓⁿ` is an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_integersModPowReductionAmbient_map (hn : n ≠ 0)
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} (f : K ⟶ L)
    (h : IsIso ((integersModPowReductionAmbient ℓ E n X).map f)) : IsIso f := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  suffices IsIso ((boundedConstructible _).ι.map f) from
    isIso_of_reflects_iso f (boundedConstructible _).ι
  obtain ⟨C, g, δ, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle ((boundedConstructible _).ι.map f)
  have hC : boundedConstructible _ C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT K.property L.property
  have hz : Limits.IsZero ((integersModPowReductionAmbient ℓ E n X).obj ⟨C, hC⟩) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n))).map_distinguished _
        hT)).2 h
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 ((boundedConstructible _).ι.map_isZero
    (isZero_of_isZero_integersModPowReductionAmbient_obj ℓ E n X hn hz))

attribute [local instance] DerivedCategory.braidedCategory'

/-- The braided structure on the derived reduction modulo `ℓⁿ`, for the Koszul braidings
`DerivedCategory.braidedCategory'`, whose monoidal structure is
`leftDerivedIntegersModPowReductionMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedIntegersModPowReductionBraided :
    L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).Braided :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction X.left ℓ E.1 n)
  (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctorBraided
    (Mod.extendScalars_map_braiding_hom_δ (integersModPowReduction X.left ℓ E.1 n))

/-- **Biduality along the reduction modulo `ℓⁿ`** (blueprint `theorem-verdier-biduality`,
(ii)): for `n ≠ 0`, the double-dual morphism `δ_{K₀}` of a bounded constructible `𝒪_E`-complex is
an isomorphism as soon as the double-dual morphism of its reduction `R K₀`, relative to the
reduction `R ω_{X, 𝒪_E}` of the dualizing complex, is one. -/
theorem isIso_verdierBiduality_of_isIso_toIhomIhom_reduction (hn : n ≠ 0)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : IsIso (toIhomIhom
      ((integersModPowReductionAmbient ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      ((integersModPowReductionAmbient ℓ E n X).obj K₀))) :
    IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀) := by
  let := PadicIntegersRingObj.boundedConstructibleBraiding ℓ E.1 X
  let G := integersModPowReductionAmbient ℓ E n X
  have hG (A B : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
      IsIso ((Functor.LaxMonoidal.ihomComparison G A).app B) := by
    rw [ObjectProperty.ihomComparison_ι_comp_app]
    -- the instances agree up to reducible unfolding; a default `exact` takes minutes
    with_reducible exact isIso_ihomComparison_integersModPowReduction ℓ E n X A B
  let := leftDerivedIntegersModPowReductionBraided ℓ E n X
  have (A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
      IsIso (dualComparison G (𝟙 (G.obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))) A) := by
    rw [dualComparison]
    have := hG A (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)
    infer_instance
  exact isIso_of_isIso_integersModPowReductionAmbient_map ℓ E n X hn _
    ((isIso_map_toIhomIhom_iff G (𝟙 _) K₀).2 h)

end AlgebraicGeometry.ProEtale.CondensedRing
