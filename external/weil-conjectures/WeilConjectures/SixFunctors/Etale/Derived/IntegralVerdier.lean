/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualBound

/-!
# Verdier biduality at the integral stage

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`,
`I = 𝔪_E`), and `X` separated of finite type over `k` with structure morphism `a_X`. The integral
dualizing complex `ω_{X, 𝒪_E} = R lim_n Res_n Ra_{X,n}^! A_n` is the point of a homotopy limit
cone of the tower `n ↦ Ra_X^!(Λ ⧸ Iⁿ)` (restriction of scalars commuting with `Ra_X^!`), and the
integral Verdier dual is `𝔻_X = RHom(-, ω_X)`. This file records the integral stage of blueprint
`theorem-verdier-biduality` (`AlgebraicGeometry.Etale.verdierDual_integralStage`), deduced, as in
the blueprint, from integral Verdier duality (`theorem-verdier-biduality--2`,
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom_dualizing`), which belongs to the
coefficient chapter.

## Implementation notes

As elsewhere in the repository
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`), the Tor amplitude of
the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` is measured over `Λ`, after restriction of scalars. Since
`Λ ⧸ Iⁿ⁺¹ ⊗ᴸ_Λ Λ ⧸ Iⁿ⁺¹ ≅ Λ ⧸ Iⁿ⁺¹ ⊕ Λ ⧸ Iⁿ⁺¹[1]`, a Tor interval `[a, b]` over `Λ` of the
restriction of an `A_n`-complex is the interval `[a + 1, b]` over `A_n`, and conversely `[α, β]`
over `A_n` gives `[α - 1, β]` over `Λ`. The finite-stage dual interval `[-b - 2d, -a]` of the
blueprint therefore reads `[-b - 2d - 1, -a - 1]` in this convention.

The exceptional inverse image `Ra_X^!` over `Λ` is the right adjoint of `Ra_{X!}`, so it is defined
under the hypothesis that `Ra_{X!}` is a left adjoint, taken as an instance argument (it is a
theorem for torsion coefficients, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

attribute [local instance] _root_.DerivedCategory.braidedCategory'

section DoubleDual

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The double-dual morphism `δ_K : K ⟶ RHom(RHom(K, ω), ω)` into an arbitrary object `ω` of
`D(X_ét)`, written with `AlgebraicGeometry.Etale.derivedHom`: it is
`CategoryTheory.MonoidalClosed.toIhomIhom` for the derived braiding. Stating results at a
concrete coefficient ring through this constant keeps the instance-found monoidal closed
structure out of their types (see `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). -/
noncomputable def derivedHomDoubleDual
    (ω K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ ((derivedHom A X).obj (op (((derivedHom A X).obj (op K)).obj ω))).obj ω :=
  MonoidalClosed.toIhomIhom ω K

lemma derivedHomDoubleDual_eq (ω K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedHomDoubleDual A X ω K = MonoidalClosed.toIhomIhom ω K :=
  rfl

end DoubleDual

section GlobalDuality

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

private lemma iv_globalDuality {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![A]).IsLeftAdjoint]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hπ : ∀ T, Function.Bijective (fun a : (R(f)_![A]).obj
        (((derivedTensor A X).obj K).obj ((L((f)^*[A])).obj T)) ⟶ N ↦
      ((projectionMap A f).app K).app T ≫ a)) :
    Nonempty ((R((f)_*[A])).obj (((derivedHom A X).obj (op K)).obj
        ((R(f)_![A]).rightAdjoint.obj N)) ≅
      ((derivedHom A Y).obj (op ((R(f)_![A]).obj K))).obj N) := by
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![A])
  let e (T : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :=
    ((derivedUpperStarLowerStarAdjunction A f).homEquiv T _).symm.trans <|
      ((derivedTensorHomAdjunction A K).homEquiv _ _).symm.trans <|
        (adj.homEquiv _ N).symm.trans <|
          (Equiv.ofBijective _ (hπ T)).trans <|
            (derivedTensorHomAdjunction A ((R(f)_![A]).obj K)).homEquiv T N
  refine nonempty_iso_of_homEquiv e ?_
  intro T T' g h
  simp only [e, Equiv.trans_apply, Adjunction.homEquiv_naturality_left_symm,
    Equiv.ofBijective_apply]
  have hnat : ((projectionMap A f).app K).app T' ≫
      (R(f)_![A]).map (((derivedTensor A X).obj K).map ((L((f)^*[A])).map g)) =
      ((derivedTensor A Y).obj ((R(f)_![A]).obj K)).map g ≫
        ((projectionMap A f).app K).app T :=
    (((projectionMap A f).app K).naturality g).symm
  rw [← Category.assoc, hnat, Category.assoc]
  exact (derivedTensorHomAdjunction A ((R(f)_![A]).obj K)).homEquiv_naturality_left g _

end GlobalDuality

/-! Private ingredients for the integral dualizing object. -/

private lemma iv_quotientPow_exponent {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)
    (S : Scheme.{u}) [HasInvertibleExponent (Λ ⧸ I) S] (n : ℕ) :
    HasInvertibleExponent (Λ ⧸ I ^ n) S := by
  obtain ⟨m, hm, hm0, hmu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I) (X := S)
  have hmI : (m : Λ) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using hm0
  refine ⟨m ^ n, pow_pos hm n, ?_, ?_⟩
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa using Ideal.pow_mem_pow hmI n
  · simpa using hmu.pow n

private lemma iv_point_quotPowLimit {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)
    [IsAdicComplete I Λ] {k : Type u} [Field k] [IsAlgClosed k] :
    ∃ c : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I),
      Pretriangulated.IsHomotopyLimit c ∧ Nonempty (c.pt ≅ constantComplex Λ (Spec (.of k))) := by
  let T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
    Ideal.quotPowFunctor I ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0
  let c := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone (Ideal.quotPowCone I)
  have hc : IsLimit c := isLimitOfPreserves _ (Ideal.isLimitQuotPowCone I)
  have hT (n : ℕ) (i : ℤ) : Epi ((T.map (homOfLE n.le_succ).op).f i) := by
    by_cases hi : i = 0
    · subst hi
      change Epi (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op)).f 0)
      rw [HomologicalComplex.single_map_f_self]
      have : Epi ((Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op) := by
        rw [ModuleCat.epi_iff_surjective]
        exact Submodule.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _
  have hQ := _root_.DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi hT hc
  let F := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : F.IsEquivalence := (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).isEquivalence_functor
  have : F.Additive := additive_constantSheaf Λ _
  let G := F.mapDerivedCategory
  have hG := hQ.map G
  let e : HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
      _root_.DerivedCategory.Q ⋙ G ≅ F ⋙ _root_.DerivedCategory.singleFunctor _ 0 :=
    Functor.isoWhiskerRight (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).symm G ≪≫
      F.mapDerivedCategorySingleFunctor 0
  let eT : T ⋙ _root_.DerivedCategory.Q ⋙ G ≅
      _root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I :=
    Functor.isoWhiskerLeft (Ideal.quotPowFunctor I) e
  let c' : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I) :=
    { pt := (G.mapCone (_root_.DerivedCategory.Q.mapCone c)).pt
      π := (G.mapCone (_root_.DerivedCategory.Q.mapCone c)).π ≫ eT.hom }
  refine ⟨c', hG.of_iso eT c' (Iso.refl _) (fun n ↦ by simp [c']), ?_⟩
  exact ⟨e.app (ModuleCat.of Λ Λ) ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso F).symm ≪≫
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)⟩

private lemma iv_reduction_constant {Λ : Type (u + 1)} [CommRing Λ]
    (X : Scheme.{u}) (J : Ideal Λ) :
    Nonempty ((reductionModIdeal Λ X J).obj (constantComplex Λ X) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ J)))) :=
  ⟨λ_ _⟩

private lemma iv_extend_constant {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})
    (J : Ideal Λ) {a : Λ} (ha : J = Ideal.span {a}) :
    Nonempty ((derivedExtendScalars (Ideal.Quotient.mk_surjective)
        (by rw [Ideal.mk_ker, ha]) X).obj (constantComplex Λ X) ≅
      constantComplex (Λ ⧸ J) X) := by
  have := preservesKFlatQuasiIso_extendScalars (Ideal.Quotient.mk_surjective)
    (show RingHom.ker (Ideal.Quotient.mk J) = Ideal.span {a} by rw [Ideal.mk_ker, ha]) X
  have := Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := Ideal.Quotient.mk J)
  let :=
    (Sheaf.extendScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).leftDerivedFunctorMonoidal
  exact ⟨(Functor.Monoidal.εIso
    (Sheaf.extendScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).leftDerivedFunctor).symm⟩

private lemma iv_reduction_of_baseChange {Λ : Type (u + 1)} [CommRing Λ]
    (X : Scheme.{u}) (J : Ideal Λ) {a : Λ} (ha : J = Ideal.span {a})
    {K : 𝐃(X, Λ)} {Kn : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk J) X).obj Kn}
    (hη : IsDerivedBaseChange η) :
    Nonempty ((reductionModIdeal Λ X J).obj K ≅
      (derivedRestrictScalars (Ideal.Quotient.mk J) X).obj Kn) := by
  have hker : RingHom.ker (Ideal.Quotient.mk J) = Ideal.span {a} := by
    rw [Ideal.mk_ker, ha]
  obtain ⟨e⟩ := nonempty_iso_derivedExtendScalars_of_isDerivedBaseChange
    Ideal.Quotient.mk_surjective hker X hη
  obtain ⟨e'⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars
    Ideal.Quotient.mk_surjective hker X K
  let z := (_root_.DerivedCategory.singleFunctor _ 0).mapIso
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (Ideal.quotientEquivAlgOfEq Λ (Ideal.mk_ker (I := J))).toLinearEquiv.toModuleIso)
  let e'' : (derivedRestrictScalars (Ideal.Quotient.mk J) X).obj
      ((derivedExtendScalars Ideal.Quotient.mk_surjective hker X).obj K) ≅
      (reductionModIdeal Λ X J).obj K :=
    e' ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso z
  exact ⟨e''.symm ≪≫ (derivedRestrictScalars (Ideal.Quotient.mk J) X).mapIso e⟩

private lemma iv_finite_dualizing_bound {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
          (constantComplex Λ (Spec (.of k)))) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-2 * (d : ℤ)) 0
        ((R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
          (constantComplex Λ (Spec (.of k)))) := by
  have hUbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (constantComplex Λ X) :=
    (DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)
  have hUt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      (constantComplex Λ X) :=
    (DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  have h := boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed Λ aX d hd hUbc hUt
  let e : (verdierDual Λ aX).obj (op (constantComplex Λ X)) ≅
      (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
        (constantComplex Λ (Spec (.of k))) :=
    (MonoidalClosed.unitNatIso.app (dualizingComplex Λ aX)).symm ≪≫
      ((Adjunction.rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint (R(aX)_![ModuleCat.{u + 1} Λ]))
        (rightDerivedUpperShriekAdjunction Λ aX)).app (constantComplex Λ (Spec (.of k)))).symm
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e h.1,
    (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e (by simpa using h.2)⟩

private lemma iv_quotPow_orthogonal {Λ : Type (u + 1)} [CommRing Λ]
    {X S : Scheme.{u}} {I : Ideal Λ} {ϖ : Λ} (hϖI : ϖ ∈ I)
    (G : 𝐃(S, Λ) ⥤ 𝐃(X, Λ)) [G.Additive] [G.Linear Λ]
    {c : Cone (_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙ G)}
    (hc : Pretriangulated.IsHomotopyLimit c) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal c.pt := by
  have hkill (n : ℕ) : ϖ ^ n • 𝟙
      ((_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙ G).obj (op n)) = 0 := by
    change ϖ ^ n • 𝟙 (G.obj _) = 0
    rw [← G.map_id, ← Functor.map_smul,
      _root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n, G.map_zero]
  intro Z f hZ
  exact hc.hom_ext_zero (fun n g ↦ hZ.hom_eq_zero (hkill n) g)
    (fun n g ↦ (ObjectProperty.le_shift _ 1 Z hZ).hom_eq_zero (hkill n) g) f

private lemma iv_bijective_comp {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) {S T W : 𝐃(X, Λ)} (f : S ⟶ T)
    (hf : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map f))
    (hW : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal W) :
    Function.Bijective (fun a : T ⟶ W ↦ f ≫ a) := by
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hf
  exact ObjectProperty.bijective_comp_of_distinguished hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC) hW

universe v w

section IntegralVerdierHomNotation

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

end IntegralVerdierHomNotation

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI in
/-- Blueprint `proposition-sp-integral-adjunction`: The integral dualizing object and its
adjunction.

For `a_X : X ⟶ Spec k` separated of finite type, `k` algebraically closed, there is a derived
complete object `ω_{X, 𝒪_E} = R lim_n Res_n Ra_{X,n}^! A_n`, realised as the point of a homotopy
limit cone `ω` of the tower `n ↦ Ra_X^!(Λ ⧸ Iⁿ)` (restriction of scalars commuting with
`Ra_X^!`), such that:

1. its reductions are `ω ⊗ᴸ A_n ≅ Ra_X^!(Λ ⧸ Iⁿ)`;
2. `ω ∈ Dᵇc(X, 𝒪_E)`, and if `dim X ≤ d` its reductions have Tor amplitude in `[-2d - 1, 0]`
   (the interval `[-2d, 0]` of the blueprint, measured over `A_n`; see the module
   documentation);
3. for `K ∈ Dᵇc(X, 𝒪_E)` there is an isomorphism of derived mapping complexes
   `Ra_{X*} RHom(K, ω) ≅ RHom(Ra_{X!} K, Λ)`. -/
theorem exists_isHomotopyLimit_dualizing :
    ∃ ω : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint), Pretriangulated.IsHomotopyLimit ω ∧
      (∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj ω.pt ≅
        (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
          ((DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I).obj (op n)))) ∧
      DerivedCategory.boundedConstructibleIntegral I X ω.pt ∧
      (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ n : ℕ,
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-2 * (d : ℤ) - 1) 0
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj ω.pt)) ∧
      ∀ K : 𝐃(X, Λ), DerivedCategory.boundedConstructibleIntegral I X K →
        Nonempty ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ω.pt) ≅
          ((derivedHom (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
            (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))).obj
              (constantComplex Λ (Spec (.of k)))) := by
  classical
  have hϖ : ϖ ∈ nonZeroDivisors Λ :=
    mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.ne_zero hϖ)
  subst hI
  let S := Spec (.of k)
  let adj := Adjunction.ofIsLeftAdjoint (R(aX)_![ModuleCat.{u + 1} Λ])
  let G := (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : G.Additive := adj.right_adjoint_additive
  have : G.Linear Λ := adj.right_adjoint_linear
  obtain ⟨c, hc, ⟨e⟩⟩ := iv_point_quotPowLimit (k := k) (Ideal.span {ϖ})
  let ω := G.mapCone c
  have hω : Pretriangulated.IsHomotopyLimit ω := hc.map G
  let eω : ω.pt ≅ G.obj (constantComplex Λ S) := G.mapIso e
  have hϖI : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
  have hωc : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology (Ideal.span {ϖ}) ω.pt :=
    _root_.DerivedCategory.derivedComplete_of_rightOrthogonal hϖ rfl
      (iv_quotPow_orthogonal hϖI G hω)
  have hred (n : ℕ) : Nonempty ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj ω.pt ≅
      G.obj ((_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology
        (Ideal.span {ϖ})).obj (op n))) := by
    obtain ⟨e₁⟩ := nonempty_iso_map_reductionModIdeal G hϖ n (constantComplex Λ S)
    obtain ⟨e₂⟩ := iv_reduction_constant S (Ideal.span {ϖ} ^ n)
    exact ⟨(reductionModIdeal Λ X _).mapIso eω ≪≫ e₁.symm ≪≫ G.mapIso e₂⟩
  have hfin (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (n : ℕ) :
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).obj ω.pt) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-2 * (d : ℤ) - 1) 0
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ (n + 1))).obj ω.pt) := by
    let J := Ideal.span {ϖ} ^ (n + 1)
    have hJ : J = Ideal.span {ϖ ^ (n + 1)} := by
      dsimp only [J]
      rw [Ideal.span_singleton_pow]
    have hker : RingHom.ker (Ideal.Quotient.mk J) = Ideal.span {ϖ ^ (n + 1)} := by
      rw [Ideal.mk_ker, hJ]
    let : Finite (Λ ⧸ J) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (n + 1)
    let : HasInvertibleExponent (Λ ⧸ J) S :=
      iv_quotientPow_exponent (Ideal.span {ϖ}) S (n + 1)
    obtain ⟨eU⟩ := iv_extend_constant S J hJ
    have hη := (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit
      Ideal.Quotient.mk_surjective hker S (constantComplex Λ S)).comp_map_iso eU
    obtain ⟨θ, hθ⟩ := (coefficientChangeCompatibility.reduction hϖ (n + 1)).rightDerivedUpperShriek
      aX (constantComplex Λ S) (constantComplex (Λ ⧸ J) S) _ hη
    obtain ⟨eθ⟩ := iv_reduction_of_baseChange X J hJ hθ
    let er := (reductionModIdeal Λ X J).mapIso eω ≪≫ eθ
    obtain ⟨hbc, ht⟩ := iv_finite_dualizing_bound (Λ := Λ ⧸ J) aX d hd
    have hbc' := (boundedConstructible_derivedRestrictScalars_iff J _).2 hbc
    have ht' := torAmplitudeIn_derivedRestrictScalars Ideal.Quotient.mk_surjective hker
      ((nonZeroDivisors Λ).pow_mem hϖ (n + 1)) ht
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso er.symm hbc',
      (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso er.symm ht'⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  refine ⟨ω, hω, hred, ⟨hωc, -2 * (d : ℤ) - 1, 0, hfin d hd⟩,
    fun d hd n ↦ (hfin d hd n).2, ?_⟩
  intro K _hK
  have hS : (_root_.DerivedCategory.smulInvertible S.smallEtaleTopology ϖ).rightOrthogonal
      (constantComplex Λ S) := by
    have hcorth := iv_quotPow_orthogonal hϖI (𝟭 𝐃(S, Λ)) hc
    intro Z f hZ
    apply (cancel_mono e.inv).mp
    rw [Limits.zero_comp]
    exact hcorth (f ≫ e.inv) hZ
  let : Finite (Λ ⧸ Ideal.span {ϖ} ^ 1) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) 1
  obtain ⟨eH⟩ := iv_globalDuality (ModuleCat.{u + 1} Λ) aX K (constantComplex Λ S)
    (fun T ↦ iv_bijective_comp hϖ _ (by
      have hp : IsIso ((reductionModIdeal Λ S (Ideal.span {ϖ} ^ 1)).map
          (((projectionMap (ModuleCat.{u + 1} Λ) aX).app K).app T)) := by
        simpa only [projectionMapApp_eq] using
          isIso_reductionModIdeal_map_projectionMap_of_finite hϖ 1 aX K T
      exact (congrArg (fun J : Ideal Λ ↦ IsIso ((reductionModIdeal Λ S J).map
        (((projectionMap (ModuleCat.{u + 1} Λ) aX).app K).app T))) (pow_one _)).mp hp) hS)
  exact ⟨(R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso
    (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).mapIso eω) ≪≫ eH⟩

variable
  (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
    (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint))
  (hωX : Pretriangulated.IsHomotopyLimit ωX)

include hϖ hI hωX in
/-- Blueprint `theorem-verdier-biduality--2`: Integral Verdier duality.

For `K ∈ Dᵇc(X, 𝒪_E)` and the integral dualizing complex `ω_X` (the point of a homotopy limit
cone of `n ↦ Ra_X^!(Λ ⧸ Iⁿ)`), the integral Verdier dual `𝔻_X K = RHom(K, ω_X)`:

1. lies in `Dᵇc(X, 𝒪_E)`;
2. has reductions `(𝔻_X K) ⊗ᴸ A_n ≅ 𝔻_{X,n} K_n`, read after restriction of scalars as
   `RHom(K, Ra_X^!(Λ ⧸ Iⁿ))`;
3. if `dim X ≤ d` and the reductions of `K` have Tor amplitude in `[a, b]`, the reductions of
   `𝔻_X K` have Tor amplitude in `[-b - 2d - 1, -a - 1]` (the interval `[-b - 2d, -a]` of the
   blueprint, measured over `A_n`; see the module documentation);
4. the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
theorem boundedConstructibleIntegral_derivedHom_dualizing {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I X
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ∧
      (∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ≅
        ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj
          ((R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
            ((DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I).obj (op n))))) ∧
      (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
          (-b - 2 * (d : ℤ) - 1) (-a - 1)
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt))) ∧
      IsIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) X ωX.pt K) :=
  sorry

include hϖ hI hωX in
/-- Blueprint `theorem-verdier-biduality`: Verdier biduality on the coefficient class, at the
integral stage `Λ = 𝒪_E`.

For `X` separated of finite type over an algebraically closed field `k`, the integral Verdier
dual `𝔻_X = RHom(-, ω_X)` preserves `Dᵇc(X, 𝒪_E)` (which is `Dᵇc_ctf(X, 𝒪_E)`, the uniform Tor
bound being part of its definition) and the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an
isomorphism on it, so that `𝔻_X` is an exact anti-equivalence of `Dᵇc(X, 𝒪_E)`; the uniform
reduction Tor interval `[a, b]` gives `[-b - 2d - 1, -a - 1]` for the dual (measured over `Λ`).
As in the blueprint this is integral Verdier duality
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom_dualizing`). The finite stages
are `AlgebraicGeometry.Etale.verdierDual_finiteStage`. -/
theorem verdierDual_integralStage :
    (∀ {K : 𝐃(X, Λ)}, DerivedCategory.boundedConstructibleIntegral I X K →
      DerivedCategory.boundedConstructibleIntegral I X
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ∧
        IsIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) X ωX.pt K)) ∧
    ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ) {K : 𝐃(X, Λ)},
      DerivedCategory.boundedConstructibleIntegral I X K →
      (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
      ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
        (-b - 2 * (d : ℤ) - 1) (-a - 1)
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt)) :=
  ⟨fun hK ↦ ⟨(boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).1,
      (boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).2.2.2⟩,
    fun d hd a b _ hK hab ↦
      (boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).2.2.1 d hd a b hab⟩

end Etale

end AlgebraicGeometry
