/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual

/-!
# Duals of complexes with finite locally constant cohomology

Let `λ` be a finite field and `C` a bounded complex of étale `λ`-sheaves on a scheme `T` whose
cohomology sheaves are finite locally constant (blueprint
`lemma-smooth-morphisms-locally-constant-sheaves`). Then the derived dual `C^∨ = RHom(C, λ_T)` has
finite locally constant cohomology sheaves `H^q(C^∨) ≅ 𝓗om(H^{-q}(C), λ_T)`, and for every morphism
`v : T' ⟶ T` the canonical comparison `Lv^*(C^∨) ⟶ (Lv^* C)^∨`
(`AlgebraicGeometry.Etale.coefficientDualComparison`) is an isomorphism.

A finite locally constant sheaf `E` over a field is flat and dualizable with dual `[E, λ]`
(`AlgebraicGeometry.Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf`), hence so is `E`
placed in any degree in the derived category; this is the base case. The general case is a
dévissage along the truncation triangles `τ^{≤m} C ⟶ C ⟶ H^{m+1}(C)[-m-1] ⟶`: the cohomology
of the duals of the two outer terms lives in disjoint ranges of degrees, so that the long exact
cohomology sequences split into isomorphisms, without any compatibility of the connecting maps.

The dévissage is carried out for a general coefficient category and a class of dualizable sheaves
(`AlgebraicGeometry.Etale.DualizableSheafClass`), and only specialised to `ModuleCat λ` at the
end: see the implementation notes of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.

## Main statements

- `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_coefficientDual`
- `AlgebraicGeometry.Etale.isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open Pretriangulated

/-- In a distinguished triangle `T`, `H^{n₁}(T.mor₁)` is an isomorphism if `H^{n₀}` and
`H^{n₁}` of the third object vanish, `n₀ + 1 = n₁`. -/
lemma isIso_homologyMap_mor₁_of_isZero (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₃))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₃)) :
    IsIso ((homologyFunctor C n₁).map T.mor₁) := by
  have : Mono ((homologyFunctor C n₁).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT n₀ n₁ h).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C n₁).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT n₁).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle `T`, `H^{n₀}(T.mor₂)` is an isomorphism if `H^{n₀}` and
`H^{n₁}` of the first object vanish, `n₀ + 1 = n₁`. -/
lemma isIso_homologyMap_mor₂_of_isZero (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₁)) :
    IsIso ((homologyFunctor C n₀).map T.mor₂) := by
  have : Mono ((homologyFunctor C n₀).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n₀).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C n₀).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n₀ n₁ h).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end DerivedCategory

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

section Generic

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

/-- The internal-hom comparison is natural in the first variable. -/
@[reassoc]
lemma derivedHomUpperStarComparison_naturality_left {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K')
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((g)^*[A])).map (((RHom(X)[A]).map f.op).app M) ≫ derivedHomUpperStarComparison A g K M =
      derivedHomUpperStarComparison A g K' M ≫
        ((RHom(Y)[A]).map ((L((g)^*[A])).map f).op).app ((L((g)^*[A])).obj M) :=
  letI := leftDerivedUpperStarMonoidal A g
  -- Rewriting to the form of the generic statement first (and giving `L((g)^*[A])` explicitly)
  -- keeps the kernel from unfolding the derived internal hom to compare the two sides.
  have h (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      derivedHomUpperStarComparison A g K M =
        (Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).app M := rfl
  have hX : (RHom(X)[A]).map f.op = MonoidalClosed.pre f := rfl
  have hY : (RHom(Y)[A]).map ((L((g)^*[A])).map f).op =
      MonoidalClosed.pre ((L((g)^*[A])).map f) := rfl
  by
    rw [hX, hY, h, h]
    exact Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app L((g)^*[A]) f M

/-- The canonical comparison `Lg^*(K^∨) ⟶ (Lg^* K)^∨` of coefficient duals: the internal-hom
comparison `Lg^* RHom(K, Λ) ⟶ RHom(Lg^* K, Lg^* Λ)` followed by `Lg^* Λ ≅ Λ`. -/
noncomputable def coefficientDualComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((g)^*[A])).obj ((coefficientDual A X).obj (op K)) ⟶
      (coefficientDual A Y).obj (op ((L((g)^*[A])).obj K)) :=
  derivedHomUpperStarComparison A g K (𝟙_ _) ≫
    ((RHom(Y)[A]).obj (op ((L((g)^*[A])).obj K))).map (leftDerivedUpperStarUnitIso A g).hom

lemma isIso_coefficientDualComparison_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (coefficientDualComparison A g K) ↔
      IsIso (derivedHomUpperStarComparison A g K (𝟙_ _)) := by
  rw [coefficientDualComparison, isIso_comp_right_iff]

/-- The comparison of coefficient duals is natural. -/
@[reassoc]
lemma coefficientDualComparison_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K') :
    (L((g)^*[A])).map ((coefficientDual A X).map f.op) ≫ coefficientDualComparison A g K =
      coefficientDualComparison A g K' ≫
        (coefficientDual A Y).map ((L((g)^*[A])).map f).op := by
  rw [coefficientDualComparison, coefficientDualComparison, Category.assoc]
  erw [derivedHomUpperStarComparison_naturality_left_assoc]
  congr 1
  exact (((RHom(Y)[A]).map ((L((g)^*[A])).map f).op).naturality
    (leftDerivedUpperStarUnitIso A g).hom).symm

lemma isIso_coefficientDualComparison_iff_of_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K') :
    IsIso (coefficientDualComparison A g K) ↔ IsIso (coefficientDualComparison A g K') := by
  rw [isIso_coefficientDualComparison_iff, isIso_coefficientDualComparison_iff,
    isIso_derivedHomUpperStarComparison_iff_of_iso_left A g e]

/-- The comparison of coefficient duals is an isomorphism at an object with a left dual. -/
lemma isIso_coefficientDualComparison_of_exactPairing {X Y : Scheme.{u}} (g : Y ⟶ X)
    (D P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing D P] :
    IsIso (coefficientDualComparison A g P) := by
  rw [isIso_coefficientDualComparison_iff]
  exact isIso_derivedHomUpperStarComparison_of_exactPairing A g D P _

omit [UpperStarPreservesFlat A] in
/-- The coefficient dual sends distinguished triangles to distinguished triangles. -/
lemma exists_distTriang_coefficientDual {X : Scheme.{u}}
    (T : Pretriangulated.Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Pretriangulated.Triangle.mk ((coefficientDual A X).map T.mor₂.op)
      ((coefficientDual A X).map T.mor₁.op) w ∈ distTriang _ :=
  exists_distTriang_derivedHom_left (𝟙_ _) T hT

omit [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
/-- The internal dual of a zero sheaf is zero. -/
lemma isZero_ihom_obj_of_isZero {X : Scheme.{u}} {E : Sheaf X.smallEtaleTopology A} (hE : IsZero E)
    (F : Sheaf X.smallEtaleTopology A) : IsZero ((ihom E).obj F) := by
  rw [IsZero.iff_id_eq_zero]
  apply MonoidalClosed.uncurry_injective
  have : IsZero (E ⊗ (ihom E).obj F) := by
    rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hE.eq_of_src (𝟙 E) 0,
      MonoidalPreadditive.zero_whiskerRight]
  exact this.eq_of_src _ _

omit [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
/-- Vanishing of the cohomology of a dual from the description of its cohomology sheaves. -/
lemma isZero_homology_of_nonempty_iso {T : Scheme.{u}}
    (C D : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) (p : ℤ)
    (h : Nonempty ((_root_.DerivedCategory.homologyFunctor _ p).obj D ≅
      (ihom ((_root_.DerivedCategory.homologyFunctor _ (-p)).obj C)).obj (𝟙_ _)))
    (hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ (-p)).obj C)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj D) :=
  (isZero_ihom_obj_of_isZero A hz _).of_iso h.some

omit [UpperStarPreservesFlat A] in
/-- Transport of the description of the cohomology of a dual along a map `C ⟶ Y` inducing
isomorphisms on `H^{-q}` and on `H^q` of the duals. -/
lemma nonempty_homology_dual_iso_of_map {T : Scheme.{u}}
    {C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : C ⟶ Y) (q : ℤ)
    [IsIso ((_root_.DerivedCategory.homologyFunctor _ q).map ((coefficientDual A T).map φ.op))]
    [IsIso ((_root_.DerivedCategory.homologyFunctor _ (-q)).map φ)]
    (hY : Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((coefficientDual A T).obj (op Y)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj Y)).obj (𝟙_ _))) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((coefficientDual A T).obj (op C)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj (𝟙_ _)) :=
  ⟨(asIso ((_root_.DerivedCategory.homologyFunctor _ q).map
      ((coefficientDual A T).map φ.op))).symm ≪≫ hY.some ≪≫
    ((MonoidalClosed.internalHom).mapIso
      (asIso ((_root_.DerivedCategory.homologyFunctor _ (-q)).map φ)).op).app (𝟙_ _)⟩

omit [UpperStarPreservesFlat A] in
/-- Transport of the description of the cohomology of a dual along a map `X ⟶ C` inducing
isomorphisms on `H^{-q}` and on `H^q` of the duals. -/
lemma nonempty_homology_dual_iso_of_map' {T : Scheme.{u}}
    {X C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : X ⟶ C) (q : ℤ)
    [IsIso ((_root_.DerivedCategory.homologyFunctor _ q).map ((coefficientDual A T).map φ.op))]
    [IsIso ((_root_.DerivedCategory.homologyFunctor _ (-q)).map φ)]
    (hX : Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((coefficientDual A T).obj (op X)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj X)).obj (𝟙_ _))) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((coefficientDual A T).obj (op C)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj (𝟙_ _)) :=
  ⟨asIso ((_root_.DerivedCategory.homologyFunctor _ q).map
      ((coefficientDual A T).map φ.op)) ≪≫ hX.some ≪≫
    ((MonoidalClosed.internalHom).mapIso
      (asIso ((_root_.DerivedCategory.homologyFunctor _ (-q)).map φ)).symm.op).app (𝟙_ _)⟩

-- The steps of the dévissages below are separate declarations, which keeps the memory used by
-- each kernel check small.
omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_homology`: below degree `-(m + 1)`, the dual of
`C ⟶ Y` induces isomorphisms on cohomology. -/
private lemma dual_step_homology_aux₁ {T : Scheme.{u}}
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hXz : ∀ q, m < q → IsZero ((homologyFunctor _ q).obj X))
    (hXd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op X)) ≅
      (ihom ((homologyFunctor _ (-q)).obj X)).obj (𝟙_ _))) (q : ℤ) (hq : q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map ((coefficientDual A T).map g'.op)) := by
  obtain ⟨w, hw⟩ := exists_distTriang_coefficientDual A _ hT
  exact isIso_homologyMap_mor₁_of_isZero _ hw (q - 1) q (by omega)
    (isZero_homology_of_nonempty_iso A _ _ _ (hXd _) (hXz _ (by omega)))
    (isZero_homology_of_nonempty_iso A _ _ _ (hXd _) (hXz _ (by omega)))

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_homology`: above degree `-(m + 1)`, the dual of
`X ⟶ C` induces isomorphisms on cohomology. -/
private lemma dual_step_homology_aux₂ {T : Scheme.{u}}
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor _ q).obj Y))
    (hYd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op Y)) ≅
      (ihom ((homologyFunctor _ (-q)).obj Y)).obj (𝟙_ _))) (q : ℤ) (hq : ¬q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map ((coefficientDual A T).map f.op)) := by
  obtain ⟨w, hw⟩ := exists_distTriang_coefficientDual A _ hT
  exact isIso_homologyMap_mor₂_of_isZero _ hw q (q + 1) rfl
    (isZero_homology_of_nonempty_iso A _ _ _ (hYd _) (hYz _ (by omega)))
    (isZero_homology_of_nonempty_iso A _ _ _ (hYd _) (hYz _ (by omega)))

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- The inductive step of the dévissage, for the cohomology of the dual: for a distinguished
triangle `X ⟶ C ⟶ Y ⟶ X[1]` with `X` in degrees `≤ m` and `Y` in degree `m + 1`, the
description of the cohomology sheaves of the duals passes from `X` and `Y` to `C`. -/
lemma dual_step_homology {T : Scheme.{u}}
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hXz : ∀ q, m < q → IsZero ((homologyFunctor _ q).obj X))
    (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor _ q).obj Y))
    (hXC : ∀ q, q ≤ m → IsIso ((homologyFunctor _ q).map f))
    (hCY : ∀ q, m + 1 ≤ q → IsIso ((homologyFunctor _ q).map g'))
    (hXd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op X)) ≅
      (ihom ((homologyFunctor _ (-q)).obj X)).obj (𝟙_ _)))
    (hYd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op Y)) ≅
      (ihom ((homologyFunctor _ (-q)).obj Y)).obj (𝟙_ _))) (q : ℤ) :
    Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op C)) ≅
      (ihom ((homologyFunctor _ (-q)).obj C)).obj (𝟙_ _)) := by
  by_cases hq : q ≤ -(m + 1)
  · have := dual_step_homology_aux₁ A f g' δ hT m hXz hXd q hq
    have := hCY (-q) (by omega)
    exact nonempty_homology_dual_iso_of_map A g' q (hYd q)
  · have := dual_step_homology_aux₂ A f g' δ hT m hYz hYd q hq
    have := hXC (-q) (by omega)
    exact nonempty_homology_dual_iso_of_map' A f q (hXd q)

omit [UpperStarPreservesFlat A] in
/-- The derived pullback of a complex whose cohomology vanishes in degree `p` has vanishing
cohomology in degree `p`. -/
lemma isZero_homology_leftDerivedUpperStar_obj {S T : Scheme.{u}} (g : S ⟶ T)
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) (p : ℤ)
    (hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj C)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj ((L((g)^*[A])).obj C)) :=
  (((g)^*[A]).map_isZero hz).of_iso ((leftDerivedUpperStarHomologyFunctorIso A g p).app C).symm

/-- A class of sheaves, on all schemes, containing the zero sheaves, closed under isomorphisms
and pullbacks, whose members `F` are dualizable with dual `[F, 𝟙]`: for coefficients a finite
field, the finite locally constant sheaves. -/
structure DualizableSheafClass (P : ∀ {X : Scheme.{u}}, Sheaf X.smallEtaleTopology A → Prop) :
    Prop where
  of_isZero {X : Scheme.{u}} {F : Sheaf X.smallEtaleTopology A} : IsZero F → P F
  of_iso {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology A} : (F ≅ G) → P F → P G
  upperStar {X Y : Scheme.{u}} (g : Y ⟶ X) {F : Sheaf X.smallEtaleTopology A} :
    P F → P (((g)^*[A]).obj F)
  nonempty_exactPairing {X : Scheme.{u}} {F : Sheaf X.smallEtaleTopology A} :
    P F → Nonempty (ExactPairing ((ihom F).obj (𝟙_ _)) F)

variable {A} {P : ∀ {X : Scheme.{u}}, Sheaf X.smallEtaleTopology A → Prop}

/-- The base case: the dual of a sheaf `E` of the class, placed in degree `n`, is its internal
dual placed in degree `-n`, and its formation commutes with every pullback. -/
lemma dual_singleFunctor (hP : DualizableSheafClass A P) {X : Scheme.{u}}
    (E : Sheaf X.smallEtaleTopology A) (hE : P E) (n : ℤ) :
    Nonempty ((coefficientDual A X).obj (op ((_root_.DerivedCategory.singleFunctor _ n).obj E)) ≅
      (_root_.DerivedCategory.singleFunctor _ (-n)).obj ((ihom E).obj (𝟙_ _))) ∧
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      IsIso (coefficientDualComparison A g ((_root_.DerivedCategory.singleFunctor _ n).obj E)) := by
  let Q := (HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ) n).obj E
  have hl (m : ℤ) : P (Q.X m) := by
    by_cases hm : m = n
    · subst hm
      exact hP.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm hE
    · exact hP.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)
  let _ (m : ℤ) : HasRightDual (Q.X m) :=
    { rightDual := (ihom (Q.X m)).obj (𝟙_ _)
      exact := letI := (hP.nonempty_exactPairing (hl m)).some
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj_rightDual Q n n
  obtain ⟨_⟩ := nonempty_exactPairing_swap (_root_.DerivedCategory.Q.obj Q)
    (_root_.DerivedCategory.Q.obj (CochainComplex.rightDual Q))
  let e : (_root_.DerivedCategory.singleFunctor _ n).obj E ≅ _root_.DerivedCategory.Q.obj Q :=
    (_root_.DerivedCategory.singleFunctorIsoCompQ _ n).app E
  refine ⟨?_, fun g ↦ ?_⟩
  · obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (CochainComplex.rightDual Q) (-n)
    exact ⟨(coefficientDual A X).mapIso e.op.symm ≪≫ coefficientDualIsoOfExactPairing
      (_root_.DerivedCategory.Q.obj (CochainComplex.rightDual Q)) _ ≪≫
      _root_.DerivedCategory.Q.mapIso eM ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ (-n)).app M).symm ≪≫
      (_root_.DerivedCategory.singleFunctor _ (-n)).mapIso
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-n) M).symm ≪≫
          (HomologicalComplex.eval _ _ (-n)).mapIso eM.symm ≪≫
          ((MonoidalClosed.internalHom).mapIso (HomologicalComplex.singleObjXIsoOfEq
            (ComplexShape.up ℤ) n E (-(-n)) (neg_neg n)).op).symm.app (𝟙_ _))⟩
  · rw [isIso_coefficientDualComparison_iff_of_iso A g e]
    exact isIso_coefficientDualComparison_of_exactPairing A g
      (_root_.DerivedCategory.Q.obj (CochainComplex.rightDual Q)) _

/-- The dual of a complex whose cohomology lies in the class and is concentrated in degree
`a`. -/
lemma dual_of_homology_concentrated (hP : DualizableSheafClass A P) {T : Scheme.{u}}
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) (a : ℤ)
    (hC : ∀ q, P ((_root_.DerivedCategory.homologyFunctor _ q).obj C))
    (hz : ∀ q, q ≠ a → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj C)) :
    (∀ q, Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((coefficientDual A T).obj (op C)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj (𝟙_ _))) ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ T), IsIso (coefficientDualComparison A g C) := by
  have : C.IsGE a := by
    rw [_root_.DerivedCategory.isGE_iff]
    exact fun i hi ↦ hz i hi.ne
  have : C.IsLE a := by
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun i hi ↦ hz i hi.ne'
  obtain ⟨E, ⟨e⟩⟩ := C.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
  let eE : (_root_.DerivedCategory.homologyFunctor _ a).obj C ≅ E :=
    (_root_.DerivedCategory.homologyFunctor _ a).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ a).app E
  obtain ⟨⟨eD⟩, hρ⟩ := dual_singleFunctor hP E (hP.of_iso eE (hC a)) a
  refine ⟨fun q ↦ ?_, fun g ↦ ?_⟩
  · let e' : (coefficientDual A T).obj (op C) ≅
        (_root_.DerivedCategory.singleFunctor _ (-a)).obj ((ihom E).obj (𝟙_ _)) :=
      (coefficientDual A T).mapIso e.symm.op ≪≫ eD
    by_cases hq : q = -a
    · subst hq
      rw [neg_neg]
      exact ⟨(_root_.DerivedCategory.homologyFunctor _ (-a)).mapIso e' ≪≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-a)).app _ ≪≫
        ((MonoidalClosed.internalHom).mapIso eE.op).app (𝟙_ _)⟩
    · refine ⟨IsZero.iso ?_ (isZero_ihom_obj_of_isZero A (hz _ (by omega)) _)⟩
      refine IsZero.of_iso ?_ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e')
      obtain hq | hq := lt_or_gt_of_ne hq
      · exact _root_.DerivedCategory.isZero_of_isGE _ (-a) q hq
      · exact _root_.DerivedCategory.isZero_of_isLE _ (-a) q hq
  · rw [isIso_coefficientDualComparison_iff_of_iso A g e]
    exact hρ g

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_comparison`: below degree `-(m + 1)`, the
pullback of the dual of `C ⟶ Y` induces isomorphisms on cohomology. -/
private lemma dual_step_comparison_aux₁ {T S : Scheme.{u}} (g : S ⟶ T)
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hXz : ∀ q, m < q → IsZero ((homologyFunctor _ q).obj X))
    (hXd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op X)) ≅
      (ihom ((homologyFunctor _ (-q)).obj X)).obj (𝟙_ _))) (q : ℤ) (hq : q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map
      ((L((g)^*[A])).map ((coefficientDual A T).map g'.op))) := by
  obtain ⟨w, hw⟩ := exists_distTriang_coefficientDual A _ hT
  exact isIso_homologyMap_mor₁_of_isZero _ ((L((g)^*[A])).map_distinguished _ hw) (q - 1) q
    (by omega)
    (isZero_homology_leftDerivedUpperStar_obj A g _ _
      (isZero_homology_of_nonempty_iso A _ _ _ (hXd _) (hXz _ (by omega))))
    (isZero_homology_leftDerivedUpperStar_obj A g _ _
      (isZero_homology_of_nonempty_iso A _ _ _ (hXd _) (hXz _ (by omega))))

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_comparison`: below degree `-(m + 1)`, the
dual of the pullback of `C ⟶ Y` induces isomorphisms on cohomology. -/
private lemma dual_step_comparison_aux₂ {T S : Scheme.{u}} (g : S ⟶ T)
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hXz : ∀ q, m < q → IsZero ((homologyFunctor _ q).obj X))
    (hXd' : ∀ q, Nonempty ((homologyFunctor _ q).obj
      ((coefficientDual A S).obj (op ((L((g)^*[A])).obj X))) ≅
        (ihom ((homologyFunctor _ (-q)).obj ((L((g)^*[A])).obj X))).obj (𝟙_ _)))
    (q : ℤ) (hq : q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map
      ((coefficientDual A S).map ((L((g)^*[A])).map g').op)) := by
  obtain ⟨w', hw'⟩ := exists_distTriang_coefficientDual A _
    ((L((g)^*[A])).map_distinguished _ hT)
  exact isIso_homologyMap_mor₁_of_isZero _ hw' (q - 1) q (by omega)
    (isZero_homology_of_nonempty_iso A _ _ _ (hXd' _)
      (isZero_homology_leftDerivedUpperStar_obj A g _ _ (hXz _ (by omega))))
    (isZero_homology_of_nonempty_iso A _ _ _ (hXd' _)
      (isZero_homology_leftDerivedUpperStar_obj A g _ _ (hXz _ (by omega))))

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_comparison`: above degree `-(m + 1)`, the
pullback of the dual of `X ⟶ C` induces isomorphisms on cohomology. -/
private lemma dual_step_comparison_aux₃ {T S : Scheme.{u}} (g : S ⟶ T)
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor _ q).obj Y))
    (hYd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op Y)) ≅
      (ihom ((homologyFunctor _ (-q)).obj Y)).obj (𝟙_ _))) (q : ℤ) (hq : ¬q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map
      ((L((g)^*[A])).map ((coefficientDual A T).map f.op))) := by
  obtain ⟨w, hw⟩ := exists_distTriang_coefficientDual A _ hT
  exact isIso_homologyMap_mor₂_of_isZero _ ((L((g)^*[A])).map_distinguished _ hw) q (q + 1) rfl
    (isZero_homology_leftDerivedUpperStar_obj A g _ _
      (isZero_homology_of_nonempty_iso A _ _ _ (hYd _) (hYz _ (by omega))))
    (isZero_homology_leftDerivedUpperStar_obj A g _ _
      (isZero_homology_of_nonempty_iso A _ _ _ (hYd _) (hYz _ (by omega))))

omit [UpperStarPreservesFlat A] in
open Pretriangulated _root_.DerivedCategory in
/-- A step of `AlgebraicGeometry.Etale.dual_step_comparison`: above degree `-(m + 1)`, the
dual of the pullback of `X ⟶ C` induces isomorphisms on cohomology. -/
private lemma dual_step_comparison_aux₄ {T S : Scheme.{u}} (g : S ⟶ T)
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor _ q).obj Y))
    (hYd' : ∀ q, Nonempty ((homologyFunctor _ q).obj
      ((coefficientDual A S).obj (op ((L((g)^*[A])).obj Y))) ≅
        (ihom ((homologyFunctor _ (-q)).obj ((L((g)^*[A])).obj Y))).obj (𝟙_ _)))
    (q : ℤ) (hq : ¬q ≤ -(m + 1)) :
    IsIso ((homologyFunctor _ q).map
      ((coefficientDual A S).map ((L((g)^*[A])).map f).op)) := by
  obtain ⟨w', hw'⟩ := exists_distTriang_coefficientDual A _
    ((L((g)^*[A])).map_distinguished _ hT)
  exact isIso_homologyMap_mor₂_of_isZero _ hw' q (q + 1) rfl
    (isZero_homology_of_nonempty_iso A _ _ _ (hYd' _)
      (isZero_homology_leftDerivedUpperStar_obj A g _ _ (hYz _ (by omega))))
    (isZero_homology_of_nonempty_iso A _ _ _ (hYd' _)
      (isZero_homology_leftDerivedUpperStar_obj A g _ _ (hYz _ (by omega))))

open Pretriangulated _root_.DerivedCategory in
/-- The inductive step of the dévissage, for the comparison of duals: for a distinguished
triangle `X ⟶ C ⟶ Y ⟶ X[1]` with `X` in degrees `≤ m` and `Y` in degree `m + 1`, if the
comparisons along `g : S ⟶ T` are isomorphisms at `X` and `Y`, and the cohomology of the duals
of `X`, `Y`, `Lg^* X` and `Lg^* Y` is described by the duals of their cohomology sheaves, then
the comparison along `g` is an isomorphism at `C`. -/
lemma dual_step_comparison {T S : Scheme.{u}} (g : S ⟶ T)
    {X C Y : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (f : X ⟶ C) (g' : C ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g' δ ∈ distTriang _)
    (m : ℤ) (hXz : ∀ q, m < q → IsZero ((homologyFunctor _ q).obj X))
    (hYz : ∀ q, q ≠ m + 1 → IsZero ((homologyFunctor _ q).obj Y))
    (hXd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op X)) ≅
      (ihom ((homologyFunctor _ (-q)).obj X)).obj (𝟙_ _)))
    (hYd : ∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op Y)) ≅
      (ihom ((homologyFunctor _ (-q)).obj Y)).obj (𝟙_ _)))
    (hXd' : ∀ q, Nonempty ((homologyFunctor _ q).obj
      ((coefficientDual A S).obj (op ((L((g)^*[A])).obj X))) ≅
        (ihom ((homologyFunctor _ (-q)).obj ((L((g)^*[A])).obj X))).obj (𝟙_ _)))
    (hYd' : ∀ q, Nonempty ((homologyFunctor _ q).obj
      ((coefficientDual A S).obj (op ((L((g)^*[A])).obj Y))) ≅
        (ihom ((homologyFunctor _ (-q)).obj ((L((g)^*[A])).obj Y))).obj (𝟙_ _)))
    (hX : IsIso (coefficientDualComparison A g X)) (hY : IsIso (coefficientDualComparison A g Y)) :
    IsIso (coefficientDualComparison A g C) := by
  rw [isIso_iff]
  intro q
  by_cases hq : q ≤ -(m + 1)
  · have h₁ := dual_step_comparison_aux₁ g f g' δ hT m hXz hXd q hq
    have h₂ := dual_step_comparison_aux₂ g f g' δ hT m hXz hXd' q hq
    have h := (homologyFunctor _ q).congr_map (coefficientDualComparison_naturality A g g')
    simp only [Functor.map_comp] at h
    have : IsIso ((homologyFunctor _ q).map
        ((L((g)^*[A])).map ((coefficientDual A T).map g'.op)) ≫
          (homologyFunctor _ q).map (coefficientDualComparison A g C)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((homologyFunctor _ q).map
      ((L((g)^*[A])).map ((coefficientDual A T).map g'.op))) _
  · have h₁ := dual_step_comparison_aux₃ g f g' δ hT m hYz hYd q hq
    have h₂ := dual_step_comparison_aux₄ g f g' δ hT m hYz hYd' q hq
    have h := (homologyFunctor _ q).congr_map (coefficientDualComparison_naturality A g f)
    simp only [Functor.map_comp] at h
    have : IsIso ((homologyFunctor _ q).map (coefficientDualComparison A g C) ≫
        (homologyFunctor _ q).map ((coefficientDual A S).map ((L((g)^*[A])).map f).op)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((homologyFunctor _ q).map
      ((coefficientDual A S).map ((L((g)^*[A])).map f).op))

open Pretriangulated _root_.DerivedCategory in
/-- The dévissage over the length of the cohomological amplitude: for a complex `C` whose
cohomology sheaves lie in the class and vanish outside `[a, a + n]`, the cohomology sheaves of
the dual are the duals of the cohomology sheaves, and the formation of the dual commutes with
every pullback. -/
theorem dual_of_homology_mem (hP : DualizableSheafClass A P) (n : ℕ) : ∀ {T : Scheme.{u}}
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) (a : ℤ),
    (∀ q, P ((homologyFunctor _ q).obj C)) →
    (∀ q, q < a ∨ a + n < q → IsZero ((homologyFunctor _ q).obj C)) →
    (∀ q, Nonempty ((homologyFunctor _ q).obj ((coefficientDual A T).obj (op C)) ≅
      (ihom ((homologyFunctor _ (-q)).obj C)).obj (𝟙_ _))) ∧
      ∀ {S : Scheme.{u}} (g : S ⟶ T), IsIso (coefficientDualComparison A g C) := by
  induction n with
  | zero =>
    intro T C a hC hz
    exact dual_of_homology_concentrated hP C a hC fun q hq ↦ hz q (by omega)
  | succ n ih =>
    intro T C a hC hz
    obtain ⟨X, Y, hX, hY, f, g', δ, hT⟩ :=
      (TStructure.t (C := Sheaf T.smallEtaleTopology A)).exists_triangle C (a + n) (a + n + 1) rfl
    have hXz : ∀ q, a + n < q → IsZero ((homologyFunctor _ q).obj X) :=
      (isLE_iff X (a + n)).1 ⟨hX⟩
    have hYz : ∀ q, q < a + n + 1 → IsZero ((homologyFunctor _ q).obj Y) :=
      (isGE_iff Y (a + n + 1)).1 ⟨hY⟩
    have hXC (q : ℤ) (hq : q ≤ a + n) : IsIso ((homologyFunctor _ q).map f) :=
      isIso_homologyMap_mor₁_of_isZero _ hT (q - 1) q (by omega) (hYz _ (by omega))
        (hYz _ (by omega))
    have hCY (q : ℤ) (hq : a + n + 1 ≤ q) : IsIso ((homologyFunctor _ q).map g') :=
      isIso_homologyMap_mor₂_of_isZero _ hT q (q + 1) rfl (hXz _ (by omega)) (hXz _ (by omega))
    have hXl (q : ℤ) : P ((homologyFunctor _ q).obj X) := by
      by_cases hq : q ≤ a + n
      · have := hXC q hq
        exact hP.of_iso (asIso ((homologyFunctor _ q).map f)).symm (hC q)
      · exact hP.of_isZero (hXz q (by omega))
    have hYl (q : ℤ) : P ((homologyFunctor _ q).obj Y) := by
      by_cases hq : a + n + 1 ≤ q
      · have := hCY q hq
        exact hP.of_iso (asIso ((homologyFunctor _ q).map g')) (hC q)
      · exact hP.of_isZero (hYz q (by omega))
    have hXz' (q : ℤ) (hq : q < a ∨ a + n < q) : IsZero ((homologyFunctor _ q).obj X) := by
      obtain hq | hq := hq
      · have := hXC q (by omega)
        exact (hz q (.inl hq)).of_iso (asIso ((homologyFunctor _ q).map f))
      · exact hXz q hq
    have hYz' (q : ℤ) (hq : q ≠ a + n + 1) : IsZero ((homologyFunctor _ q).obj Y) := by
      obtain hq | hq := lt_or_gt_of_ne hq
      · exact hYz q hq
      · have := hCY q (by omega)
        exact (hz q (.inr (by omega))).of_iso (asIso ((homologyFunctor _ q).map g')).symm
    obtain ⟨hXd, hXρ⟩ := ih X a hXl hXz'
    obtain ⟨hYd, hYρ⟩ := dual_of_homology_concentrated hP Y (a + n + 1) hYl hYz'
    refine ⟨dual_step_homology A f g' δ hT (a + n) hXz hYz' hXC hCY hXd hYd, fun {S} g ↦ ?_⟩
    have hl {Z : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
        (hZ : ∀ q, P ((homologyFunctor _ q).obj Z)) (q : ℤ) :
        P ((homologyFunctor _ q).obj ((L((g)^*[A])).obj Z)) :=
      hP.of_iso ((leftDerivedUpperStarHomologyFunctorIso A g q).app Z) (hP.upperStar g (hZ q))
    exact dual_step_comparison g f g' δ hT (a + n) hXz hYz' hXd hYd
      (ih _ a (hl hXl) fun q hq ↦ isZero_homology_leftDerivedUpperStar_obj A g X q (hXz' q hq)).1
      (dual_of_homology_concentrated hP _ (a + n + 1) (hl hYl)
        fun q hq ↦ isZero_homology_leftDerivedUpperStar_obj A g Y q (hYz' q hq)).1
      (hXρ g) (hYρ g)

end Generic

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Over a field, every étale sheaf of `Λ`-modules is flat: its stalks are vector spaces. -/
lemma flat_of_isField (hΛ : IsField Λ) {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : ObjectProperty.flat F := by
  rw [flat_iff_forall_flat_sheafFiber_obj]
  intro Ω _ _ s
  rw [ModuleCat.flat_iff_flat]
  let := hΛ.toField
  infer_instance

variable [Finite Λ]

/-- Over a finite field, the finite locally constant sheaves form a class of dualizable sheaves
in the sense of `AlgebraicGeometry.Etale.DualizableSheafClass`. -/
lemma dualizableSheafClass_isFiniteLocallyConstantSheaf (hΛ : IsField Λ) :
    DualizableSheafClass (ModuleCat.{u + 1} Λ) (fun F ↦ IsFiniteLocallyConstantSheaf F) where
  of_isZero h := IsFiniteLocallyConstantSheaf.of_isZero h
  of_iso e h := by
    have := h
    exact IsFiniteLocallyConstantSheaf.of_iso e
  upperStar {_ _} g F h := by
    have := h
    exact IsFiniteLocallyConstantSheaf.upperStar g F
  nonempty_exactPairing {_ F} h := by
    have := h
    exact ⟨exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf F (flat_of_isField hΛ F)⟩

variable {T : Scheme.{u}}

/-- Blueprint `lemma-smooth-morphisms-locally-constant-sheaves`: Duals of complexes with finite
locally constant cohomology.

Let `λ` be a finite field and `C` a bounded complex of étale `λ`-sheaves on `T` whose cohomology
sheaves are finite locally constant. Then the cohomology sheaves of the derived dual
`C^∨ = RHom(C, λ_T)` are finite locally constant, with `H^q(C^∨) ≅ 𝓗om(H^{-q}(C), λ_T)`. -/
theorem isFiniteLocallyConstantSheaf_homology_coefficientDual (hΛ : IsField Λ)
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    [C.IsGE a] [C.IsLE b]
    (hC : ∀ q, IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj C))
    (q : ℤ) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((coefficientDual _ T).obj (op C))) ∧
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((coefficientDual _ T).obj (op C)) ≅
          (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj (𝟙_ _)) := by
  have e := (dual_of_homology_mem (dualizableSheafClass_isFiniteLocallyConstantSheaf hΛ)
    (b - a).toNat C a hC fun p hp ↦ by
      obtain hp | hp := hp
      · exact _root_.DerivedCategory.isZero_of_isGE C a p hp
      · exact _root_.DerivedCategory.isZero_of_isLE C b p (by omega)).1 q
  have := isFiniteLocallyConstantSheaf_ihom_unit_of_flat _ (flat_of_isField hΛ
    ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C))
  exact ⟨IsFiniteLocallyConstantSheaf.of_iso e.some.symm, e⟩

/-- Blueprint `lemma-smooth-morphisms-locally-constant-sheaves`: Duals of complexes with finite
locally constant cohomology.

Let `λ` be a finite field and `C` a bounded complex of étale `λ`-sheaves on `T` whose cohomology
sheaves are finite locally constant. For every morphism of schemes `v : T' ⟶ T`, the canonical
morphism `Lv^*(C^∨) ⟶ (Lv^* C)^∨` is an isomorphism. -/
theorem isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf (hΛ : IsField Λ)
    (C : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    [C.IsGE a] [C.IsLE b]
    (hC : ∀ q, IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj C))
    {T' : Scheme.{u}} (v : T' ⟶ T) :
    IsIso (coefficientDualComparison _ v C) :=
  (dual_of_homology_mem (dualizableSheafClass_isFiniteLocallyConstantSheaf hΛ)
    (b - a).toNat C a hC fun p hp ↦ by
      obtain hp | hp := hp
      · exact _root_.DerivedCategory.isZero_of_isGE C a p hp
      · exact _root_.DerivedCategory.isZero_of_isLE C b p (by omega)).2 v

end AlgebraicGeometry.Etale
