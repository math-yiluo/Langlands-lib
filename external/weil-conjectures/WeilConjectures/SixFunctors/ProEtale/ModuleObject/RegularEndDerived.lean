/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantRegularEnd

/-!
# Complexes with vanishing reduction modulo a regular endomorphism

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `φ : R ⟶ S` a morphism of
commutative algebra objects and `r` an endomorphism of the regular `R`-module such that
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact. If the derived extension of scalars `S ⊗ᴸ_R K`
of `K ∈ D(Mod_R(C))` vanishes, then `r` acts invertibly on `K`, by the reduction triangle
`K --r--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`. Hence so does every integer `m` acting on the regular module as
`r ≫ ⋯ ≫ r ≫ v` for an automorphism `v`
(`CategoryTheory.Mod.isIso_zsmul_id_of_isZero_leftDerivedFunctor_extendScalars`).

Applied to a uniformizer `ϖ` of `𝒪_E`, writing `ℓ = u ϖ ^ e` with `u` a unit, this shows that
`ℓ` acts invertibly on every `𝒪_{E,X}`-complex whose first derived reduction vanishes
(`AlgebraicGeometry.ProEtale.isIso_zsmul_id_of_isZero_derivedReduction`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]

omit [MonoidalPreadditive C] in
/-- The identity of the regular module acts as the identity. -/
@[simp]
lemma regularEndSMul_id (M : Mod C R) : regularEndSMul (𝟙 (𝟙_ (Mod C R))) M = 𝟙 M := by
  simp [regularEndSMul]

omit [MonoidalPreadditive C] in
/-- The action of endomorphisms of the regular module is multiplicative. -/
lemma regularEndSMul_comp (a b : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) (M : Mod C R) :
    regularEndSMul (a ≫ b) M = regularEndSMul a M ≫ regularEndSMul b M := by
  simp [regularEndSMul]

/-- The action of endomorphisms of the regular module is `ℤ`-linear. -/
lemma regularEndSMul_zsmul (m : ℤ) (a : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) (M : Mod C R) :
    regularEndSMul (m • a) M = m • regularEndSMul a M := by
  have h : (m • a) ▷ M = m • (a ▷ M) := (MonoidalCategory.tensorRight M).map_zsmul
  rw [regularEndSMul, regularEndSMul, h, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- The identity of the regular module acts on complexes as the identity. -/
@[simp]
lemma regularEndSMulComplex_id (P : CochainComplex (Mod C R) ℤ) :
    regularEndSMulComplex (𝟙 (𝟙_ (Mod C R))) P = 𝟙 P := by
  ext i : 1
  simp

/-- The action of endomorphisms of the regular module on complexes is multiplicative. -/
lemma regularEndSMulComplex_comp (a b : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))
    (P : CochainComplex (Mod C R) ℤ) :
    regularEndSMulComplex (a ≫ b) P = regularEndSMulComplex a P ≫ regularEndSMulComplex b P := by
  ext i : 1
  simp [regularEndSMul_comp]

/-- The action of endomorphisms of the regular module on complexes is `ℤ`-linear. -/
lemma regularEndSMulComplex_zsmul (m : ℤ) (a : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))
    (P : CochainComplex (Mod C R) ℤ) :
    regularEndSMulComplex (m • a) P = m • regularEndSMulComplex a P := by
  ext i : 1
  simp [regularEndSMul_zsmul]

variable [Abelian.HasFunctorialFlatResolution C]

/-- **Integers acting through a regular endomorphism act invertibly on complexes with vanishing
reduction.** If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and the derived extension of scalars
`S ⊗ᴸ_R K` vanishes, then `r` acts invertibly on `K` (reduction triangle), hence so does every
integer `m` acting on the regular module as `r ≫ ⋯ ≫ r ≫ v` (`e` factors `r`) for an
automorphism `v`. -/
theorem isIso_zsmul_id_of_isZero_leftDerivedFunctor_extendScalars
    {r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)} (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) {K : DerivedCategory (Mod C R)}
    (hK : IsZero ((extendScalars φ).leftDerivedFunctor.obj K)) {e : ℕ}
    {v : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)} [IsIso v] {m : ℤ}
    (hm : m • 𝟙 (𝟙_ (Mod C R)) = (r ≫ ·)^[e] v) :
    IsIso (m • 𝟙 K) := by
  have := hφ.mono_f
  obtain ⟨P, π, _, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have hS := shortExact_regularEndSMulComplex w hφ P
    (fun n ↦ mono_regularEndSMul_of_flat (P.X n) (hflat n))
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let e₁ : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₃ : DerivedCategory.Q.obj
      (((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) :=
    ((comap φ).mapDerivedCategoryFactors.app
        (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C S)).app
            (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        (asIso ((extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P))).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C R)).app P ≪≫ e₁))
  have hr : IsIso (DerivedCategory.Q.map (regularEndSMulComplex r P)) :=
    (Triangle.isZero₃_iff_isIso₁ _ (DerivedCategory.triangleOfSES_distinguished hS)).1
      (((comap φ).mapDerivedCategory.map_isZero hK).of_iso e₃)
  have hF (a b : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) :
      DerivedCategory.Q.map (regularEndSMulComplex (a ≫ b) P) =
        DerivedCategory.Q.map (regularEndSMulComplex a P) ≫
          DerivedCategory.Q.map (regularEndSMulComplex b P) := by
    rw [regularEndSMulComplex_comp, Functor.map_comp]
  have hv : IsIso (DerivedCategory.Q.map (regularEndSMulComplex v P)) :=
    ⟨DerivedCategory.Q.map (regularEndSMulComplex (inv v) P), by
      rw [← hF, IsIso.hom_inv_id, regularEndSMulComplex_id, Functor.map_id], by
      rw [← hF, IsIso.inv_hom_id, regularEndSMulComplex_id, Functor.map_id]⟩
  have hpow (n : ℕ) :
      IsIso (DerivedCategory.Q.map (regularEndSMulComplex ((r ≫ ·)^[n] v) P)) := by
    induction n with
    | zero => rwa [Function.iterate_zero_apply]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hF]
      infer_instance
  have hm' : IsIso (DerivedCategory.Q.map (regularEndSMulComplex (m • 𝟙 (𝟙_ (Mod C R))) P)) := by
    rw [hm]
    exact hpow e
  rw [regularEndSMulComplex_zsmul, regularEndSMulComplex_id, Functor.map_zsmul,
    Functor.map_id] at hm'
  have hK' : m • 𝟙 K = e₁.inv ≫ (m • 𝟙 (DerivedCategory.Q.obj P)) ≫ e₁.hom := by
    simp
  rw [hK']
  infer_instance

end CategoryTheory.Mod

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The multiplication by a constant on `𝒪̲_E` is additive in the constant. -/
lemma padicIntegersRingObjMulLeft_add (a b : PadicAlgCl.integers ℓ E.1) :
    padicIntegersRingObjMulLeft.{u} ℓ E.1 (a + b) =
      padicIntegersRingObjMulLeft ℓ E.1 a + padicIntegersRingObjMulLeft ℓ E.1 b := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  ext S x
  exact ULift.ext (ContinuousMap.ext fun s ↦ add_mul a b (x.down s))

/-- The multiplication by `1` on `𝒪̲_E` is the identity. -/
lemma padicIntegersRingObjMulLeft_one :
    padicIntegersRingObjMulLeft.{u} ℓ E.1 1 = 𝟙 _ := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  ext S x
  exact ULift.ext (ContinuousMap.ext fun s ↦ one_mul (x.down s))

/-- The multiplication by a constant on `𝒪̲_E`, as an additive map in the constant. -/
noncomputable def padicIntegersRingObjMulLeftAddHom :
    PadicAlgCl.integers ℓ E.1 →+
      (padicIntegersRingObj.{u} ℓ E.1 ⟶ padicIntegersRingObj ℓ E.1) :=
  AddMonoidHom.mk' (padicIntegersRingObjMulLeft ℓ E.1) (padicIntegersRingObjMulLeft_add ℓ E)

/-- The multiplication by an integer on `𝒪̲_E` is the integer multiple of the identity. -/
lemma padicIntegersRingObjMulLeft_intCast (m : ℤ) :
    padicIntegersRingObjMulLeft.{u} ℓ E.1 m = m • 𝟙 _ := by
  have h := map_zsmul (padicIntegersRingObjMulLeftAddHom.{u} ℓ E) m 1
  rwa [padicIntegersRingObjMulLeftAddHom, AddMonoidHom.mk'_apply,
    zsmul_one, padicIntegersRingObjMulLeft_one] at h

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The multiplication by `1` on the regular `𝒪_{E,X}`-module is the identity. -/
lemma padicIntegersRegularEndOfAlgebra_one :
    padicIntegersRegularEndOfAlgebra X ℓ E.1 1 = 𝟙 _ :=
  Mod.hom_ext _ _ (by
    rw [padicIntegersRegularEnd_hom, padicIntegersMulLeft,
      Profinite.padicIntegersRingObjMulLeft_one, CategoryTheory.Functor.map_id]
    rfl)

/-- The multiplication by an integer on the regular `𝒪_{E,X}`-module is the integer multiple of
the identity. -/
lemma padicIntegersRegularEndOfAlgebra_intCast (m : ℤ) :
    padicIntegersRegularEndOfAlgebra X ℓ E.1 m = m • 𝟙 _ :=
  Mod.hom_ext _ _ (by
    rw [padicIntegersRegularEnd_hom, padicIntegersMulLeft,
      Profinite.padicIntegersRingObjMulLeft_intCast, Functor.map_zsmul,
      CategoryTheory.Functor.map_id, Mod.zsmul_hom]
    rfl)

/-- The multiplication by a power `a ^ n` of a constant of `𝒪_E` on the regular `𝒪_{E,X}`-module,
followed by an endomorphism `x`, is `x` preceded by `n` multiplications by `a`. -/
lemma padicIntegersRegularEndOfAlgebra_pow_comp (a : PadicAlgCl.integers ℓ E.1) (n : ℕ)
    (x : 𝟙_ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⟶ 𝟙_ _) :
    padicIntegersRegularEndOfAlgebra X ℓ E.1 (a ^ n) ≫ x =
      (padicIntegersRegularEndOfAlgebra X ℓ E.1 a ≫ ·)^[n] x := by
  induction n with
  | zero =>
    rw [pow_zero, padicIntegersRegularEndOfAlgebra_one, Category.id_comp,
      Function.iterate_zero_apply]
  | succ n ih =>
    rw [pow_succ', padicIntegersRegularEndOfAlgebra_mul, Category.assoc, ih,
      Function.iterate_succ_apply']

/-- The multiplication by a unit of `𝒪_E` on the regular `𝒪_{E,X}`-module is an isomorphism. -/
instance isIso_padicIntegersRegularEndOfAlgebra_unit (c : (PadicAlgCl.integers ℓ E.1)ˣ) :
    IsIso (padicIntegersRegularEndOfAlgebra X ℓ E.1 c) :=
  ⟨padicIntegersRegularEndOfAlgebra X ℓ E.1 ↑c⁻¹, by
    rw [← padicIntegersRegularEndOfAlgebra_mul, Units.mul_inv,
      padicIntegersRegularEndOfAlgebra_one], by
    rw [← padicIntegersRegularEndOfAlgebra_mul, Units.inv_mul,
      padicIntegersRegularEndOfAlgebra_one]⟩

open ZeroObject in
/-- **`ℓ` acts invertibly on `𝒪_E`-complexes with vanishing first derived reduction.** Write
`ℓ = c ϖ ^ e` for a uniformizer `ϖ` and a unit `c` of `𝒪_E`: the uniformizer acts invertibly
by the reduction triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_{E,X} ⟶ K[1]`. -/
theorem isIso_zsmul_id_of_isZero_derivedReduction
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hC : IsZero ((derivedReduction X ℓ E).obj C)) :
    IsIso ((ℓ : ℤ) • 𝟙 C) := by
  have : (derivedReduction X ℓ E).PreservesZeroMorphisms := by
    unfold derivedReduction
    infer_instance
  have h0 : IsIso ((derivedReduction X ℓ E).map (0 : C ⟶ 0)) :=
    isIso_of_source_target_iso_zero _ hC.isoZero
      ((derivedReduction X ℓ E).map_isZero (isZero_zero _)).isoZero
  have hL := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E _ h0
  have hz : IsZero
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj C) :=
    ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_isZero
      (isZero_zero _)).of_iso (asIso
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map
          (0 : C ⟶ 0)))
  have : IsDiscreteValuationRing (PadicAlgCl.integers ℓ E.1) :=
    ⟨PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E.1⟩
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2 hϖ
  have hℓ : ((ℓ : ℤ) : PadicAlgCl.integers ℓ E.1) ≠ 0 := by
    rw [Int.cast_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨e, c, hc⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hirr
  have w := padicIntegersRegularEnd_hom_comp_residueField X ℓ E.1 ϖ
    (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  refine Mod.isIso_zsmul_id_of_isZero_leftDerivedFunctor_extendScalars w
    (shortExact_padicIntegersRegularEnd X ℓ E.1 ϖ hϖ) hz
    (v := padicIntegersRegularEndOfAlgebra X ℓ E.1 c) (e := e) ?_
  rw [← padicIntegersRegularEndOfAlgebra_intCast, hc, mul_comm,
    padicIntegersRegularEndOfAlgebra_mul,
    padicIntegersRegularEndOfAlgebra_pow_comp]

end AlgebraicGeometry.ProEtale
