/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality

/-!
# Ordinary and derived duals of `R ⧸ ϖ`

Let `R` be a domain and `ϖ ≠ 0` (for instance `R = 𝒪_E` and `ϖ` a uniformizer), and
`T = R ⧸ ϖ`. The ordinary dual of `T` vanishes, while the derived dual is a shift of `T`:
`RHom_R(T, R) ≅ T[-1]` and `RHom_R(RHom_R(T, R), R) ≅ T` in `D(R)`
(`IsDiscreteValuationRing.quotient_dual_derivedDual`, blueprint
`rem-weil-biduality-coefficients`). The derived dual is computed from the distinguished triangle
`R ──ϖ──▶ R ⟶ T ⟶ R[1]` of the resolution `0 ⟶ R ⟶ R ⟶ T ⟶ 0`, the internal hom of `D(R)`
being exact in its first variable (`DerivedCategory.exists_distinguished_ihom_pre`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated
open MonoidalClosed hiding assoc id_comp comp_id

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

lemma uncurry_unitNatIso_hom_app (X : C) :
    uncurry (unitNatIso.hom.app X) = (λ_ X).hom := by
  rw [uncurry_eq]
  have := conjugateEquiv_counit (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  simpa [unitNatIso] using this

/-- Under `𝟙 ≅ [𝟙, 𝟙]`, precomposition with an endomorphism `f` of the unit is `f`. -/
@[reassoc]
lemma unitNatIso_hom_app_unit_pre_app (f : 𝟙_ C ⟶ 𝟙_ C) :
    unitNatIso.hom.app (𝟙_ C) ≫ (pre f).app (𝟙_ C) = f ≫ unitNatIso.hom.app (𝟙_ C) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, uncurry_unitNatIso_hom_app,
    unitors_equal]
  dsimp only [Functor.id_obj]
  rw [rightUnitor_naturality, ← unitors_equal, leftUnitor_naturality]

end CategoryTheory.MonoidalClosed

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  {ϖ : R}

/-- The short exact sequence `0 ⟶ R ──ϖ──▶ R ⟶ R ⧸ ϖ ⟶ 0`. -/
noncomputable def quotientShortComplex (ϖ : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.mulLeft R ϖ))
    (ModuleCat.ofHom (Ideal.span {ϖ}).mkQ) (by
      ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)))

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
lemma shortExact_quotientShortComplex (hϖ : ϖ ≠ 0) : (quotientShortComplex ϖ).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    exact ⟨y, by simpa [quotientShortComplex, mul_comm] using hy⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    simpa [quotientShortComplex, hϖ] using h
  · rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective _


open DerivedCategory ZeroObject

omit [IsDomain R] in
/-- The internal hom out of a zero object of `D(R)` vanishes. -/
lemma isZero_ihom_zero (M : DerivedCategory (ModuleCat.{u} R)) :
    IsZero ((ihom (0 : DerivedCategory (ModuleCat.{u} R))).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  have h := MonoidalClosed.pre_add_app (0 : (0 : DerivedCategory (ModuleCat.{u} R)) ⟶ 0) 0 M
  rw [add_zero, left_eq_add] at h
  rw [← NatTrans.id_app (ihom _) M, ← pre_id, ← h]
  congr 2
  exact (isZero_zero _).eq_of_src _ _

omit [IsDomain R] in
/-- `RHom(X[-1], M) ≅ RHom(X, M)[1]` in `D(R)`. -/
lemma nonempty_ihom_shift_neg_one_iso (X M : DerivedCategory (ModuleCat.{u} R)) :
    Nonempty ((ihom (X⟦(-1 : ℤ)⟧)).obj M ≅ ((ihom X).obj M)⟦(1 : ℤ)⟧) := by
  obtain ⟨h, hh⟩ := exists_distinguished_ihom_pre _
    (rot_of_distTriang _ (contractible_distinguished (X⟦(-1 : ℤ)⟧))) M
  have : IsIso h := (Triangle.isZero₂_iff_isIso₃ _ hh).1 (isZero_ihom_zero M)
  let e : X⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ X := (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by simp)).app X
  exact ⟨asIso h ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
    ((MonoidalClosed.internalHom.mapIso e.symm.op).app M)⟩

variable (ϖ) in
/-- The quotient `T = R ⧸ ϖ` as an object of `D(R)`, placed in degree `0`. -/
noncomputable abbrev quotientObj : DerivedCategory (ModuleCat.{u} R) :=
  (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ Ideal.span {ϖ}))

/-- `RHom_R(R ⧸ ϖ, R) ≅ (R ⧸ ϖ)[-1]` in `D(R)`, computed from the triangle
`R ──ϖ──▶ R ⟶ R ⧸ ϖ ⟶ R[1]`: applying `RHom(-, R)` gives the triangle
`RHom(R ⧸ ϖ, R) ⟶ R ──ϖ──▶ R ⟶ RHom(R ⧸ ϖ, R)[1]`, so that `RHom(R ⧸ ϖ, R)[1]` is a cone of
`ϖ`, as is `R ⧸ ϖ`. -/
lemma nonempty_ihom_quotientObj_iso (hϖ : ϖ ≠ 0) :
    Nonempty ((ihom (quotientObj ϖ)).obj (𝟙_ _) ≅ (quotientObj ϖ)⟦(-1 : ℤ)⟧) := by
  have hE := shortExact_quotientShortComplex hϖ
  let s := singleFunctor (ModuleCat.{u} R) 0
  let u : s.obj (ModuleCat.of R R) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} R)) :=
    singleFunctorObjUnitIso (ModuleCat.{u} R)
  let f : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ 𝟙_ _ :=
    u.inv ≫ s.map (quotientShortComplex ϖ).f ≫ u.hom
  let T₁ : Triangle (DerivedCategory (ModuleCat.{u} R)) :=
    Triangle.mk f (u.inv ≫ s.map (quotientShortComplex ϖ).g) (hE.singleδ ≫ u.hom⟦(1 : ℤ)⟧')
  have hT₁ : T₁ ∈ distTriang _ := isomorphic_distinguished _
    hE.singleTriangle_distinguished _ (Triangle.isoMk _ _ u.symm u.symm (Iso.refl _)
      (by simp [T₁, f, s]) (by simp [T₁, s]) (by
        simp only [T₁, Triangle.mk_mor₃, Iso.refl_hom,
          Category.id_comp, Category.assoc, Iso.symm_hom,
          ShortComplex.ShortExact.singleTriangle_mor₃]
        rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]))
  obtain ⟨h, hh⟩ := exists_distinguished_ihom_pre _ hT₁ (𝟙_ _)
  have hrot := rot_of_distTriang _ hh
  let e := MonoidalClosed.unitNatIso.app (𝟙_ (DerivedCategory (ModuleCat.{u} R)))
  obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ _ hT₁ hrot
    (Arrow.isoMk e e (unitNatIso_hom_app_unit_pre_app f))
  let e₃ : quotientObj ϖ ≅ ((ihom (quotientObj ϖ)).obj (𝟙_ _))⟦(1 : ℤ)⟧ :=
    Triangle.π₃.mapIso e'
  exact ⟨(shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).symm.app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm⟩

/-- Blueprint `rem-weil-biduality-coefficients`: Ordinary, derived, and geometric biduality.

For a domain `R` (e.g. `R = 𝒪_E`), `ϖ ≠ 0` (e.g. a uniformizer) and `T = R ⧸ ϖ`, ordinary
duality kills `T`, `T^* = Hom_R(T, R) = 0`, whereas the resolution `0 ⟶ R ──ϖ──▶ R ⟶ T ⟶ 0`
gives `RHom_R(T, R) ≅ T[-1]` and `RHom_R(RHom_R(T, R), R) ≅ T` in `D(R)`. These
identifications depend on the chosen `ϖ`, whence the mere existence of isomorphisms; the
canonical derived evaluation `T ⟶ RHom_R(RHom_R(T, R), R)` is an isomorphism because `T` is
perfect (`DerivedCategory.IsPerfect.isIso_toIhomIhomUnit`,
`lemma-perfect-complexes-geometric-point--8`). -/
theorem quotient_dual_derivedDual (hϖ : ϖ ≠ 0) :
    (∀ φ : Module.Dual R (R ⧸ Ideal.span {ϖ}), φ = 0) ∧
      Nonempty ((ihom (quotientObj ϖ)).obj (𝟙_ _) ≅ (quotientObj ϖ)⟦(-1 : ℤ)⟧) ∧
      Nonempty ((ihom ((ihom (quotientObj ϖ)).obj (𝟙_ _))).obj (𝟙_ _) ≅ quotientObj ϖ) := by
  obtain ⟨e⟩ := nonempty_ihom_quotientObj_iso hϖ
  obtain ⟨e'⟩ := nonempty_ihom_shift_neg_one_iso (quotientObj ϖ) (𝟙_ _)
  refine ⟨fun φ ↦ ?_, ⟨e⟩, ⟨(MonoidalClosed.internalHom.mapIso e.symm.op).app _ ≪≫ e' ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso e ≪≫ (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by simp)).app _⟩⟩
  refine LinearMap.ext fun x ↦ ?_
  have hx : ϖ • x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have := congrArg φ hx
  rw [map_smul, map_zero, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hϖ

end IsDiscreteValuationRing
