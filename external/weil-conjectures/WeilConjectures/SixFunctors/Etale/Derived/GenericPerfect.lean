/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual

/-!
# Generic perfectness of constructible complexes of finite Tor amplitude

Let `Λ` be a finite ring and `X` a noetherian scheme. Every object `K` of `Dctf(X, Λ)` is
*site-perfect on a dense open*: there is a dense open `V ⊆ X` such that on every open `W ⊆ V` the
restriction `K|_W` is dualizable in `D(W_ét, Λ)`, with a dual again in `Dctf(W, Λ)`. This is the
first step of the proof of blueprint `lemma-verdier-duality-preserves-constructibility--1`: on a
stratum on which the cohomology of `K` is finite locally constant, the finite-Tor restriction is
site-perfect (blueprint `lemma-perfect-complexes-geometric-point`).

`K` is represented by a bounded complex `P` of flat constructible sheaves
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`). Its finitely
many nonzero terms are lisse on a dense open `V`. A lisse flat sheaf is dualizable with a lisse
flat dual (`AlgebraicGeometry.Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf`,
`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_ihom_unit_of_flat`), so `P|_W` is paired in
`D(W_ét, Λ)` with its termwise dual (`DerivedCategory.nonempty_exactPairing_Q_obj_rightDual`).

## Main statements

- `AlgebraicGeometry.Etale.constructibleFiniteTor_Q_obj_of_flat`: a strictly bounded complex of
  flat constructible sheaves lies in `Dctf`.
- `AlgebraicGeometry.Etale.exists_dense_open_exactPairing`: generic perfectness.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- A strictly bounded complex of flat constructible sheaves lies in `Dctf(X, Λ)`. -/
lemma constructibleFiniteTor_Q_obj_of_flat {X : Scheme.{u}}
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hPc : ∀ n, IsConstructibleSheaf (P.X n)) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (_root_.DerivedCategory.Q.obj P) := by
  have hS := HomotopyCategory.mem_subcategory_of_strictly_bounded
    ((constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage
      _root_.DerivedCategory.Qh) P a b (fun n _ _ ↦ ?_)
  · exact (constructibleFiniteTor _ X).prop_of_iso
      ((_root_.DerivedCategory.quotientCompQhIso _).app P) hS
  have := hPc n
  exact ⟨boundedConstructible_singleFunctor_obj (P.X n) 0, 0, 0,
    torAmplitudeIn_singleFunctor_obj_of_flat Λ (P.X n) (hP n)⟩

/-- **Generic perfectness**: for a finite ring `Λ` and a complex `K` in `Dctf(X, Λ)` on a
noetherian scheme `X`, there is a dense open `V ⊆ X` such that on every open `W ⊆ V` the
restriction `K|_W` has a left dual `D` in `D(W_ét, Λ)` lying in `Dctf(W, Λ)`. This is the
site-perfectness of the finite-Tor restriction of `K` to a stratum on which its cohomology is
lisse (blueprint `lemma-perfect-complexes-geometric-point`, as used in
`lemma-verdier-duality-preserves-constructibility--1`). -/
theorem exists_dense_open_exactPairing {X : Scheme.{u}} [IsNoetherian X]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    ∃ V : X.Opens, Dense (V : Set X) ∧ ∀ W : X.Opens, W ≤ V →
      ∃ D, constructibleFiniteTor (ModuleCat.{u + 1} Λ) W D ∧
        Nonempty (ExactPairing D ((L((W.ι)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨a, b, ⟨⟨hbc, -⟩, hta⟩⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  obtain ⟨P, ⟨hPz, hPflat⟩, hPc, ⟨e⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel
    Λ a (max a b) (le_max_left a b) K hbc).1
    (hasTorAmplitudeIn_of_torAmplitudeIn (hta.mono le_rfl (le_max_right a b)))
  -- a dense open on which the finitely many nonzero terms of `P` are lisse
  have key : ∀ s : Finset ℤ, ∃ V : X.Opens, Dense (V : Set X) ∧ ∀ n ∈ s,
      IsFiniteLocallyConstantSheaf (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj (P.X n)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, by simp, by simp⟩
    | insert n s _ ih =>
      obtain ⟨V, hV, hVs⟩ := ih
      have := hPc n
      obtain ⟨U, hU, hUl⟩ := IsConstructibleSheaf.exists_dense_open (P.X n)
      refine ⟨V ⊓ U, hV.inter_of_isOpen_left hU V.isOpen, fun m hm ↦ ?_⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (V ⊓ U).ι U.ι
          (by simp) _
      · have := hVs m hm
        exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (V ⊓ U).ι V.ι
          (by simp) _
  obtain ⟨V, hVd, hV⟩ := key (Finset.Icc a (max a b))
  refine ⟨V, hVd, fun W hW ↦ ?_⟩
  -- the restriction `P'` of `P` to `W`, a bounded complex of lisse flat sheaves
  let G := (W.ι)^*[ModuleCat.{u + 1} Λ]
  let P' := (G.mapHomologicalComplex _).obj P
  have hP'l (n : ℤ) : IsFiniteLocallyConstantSheaf (P'.X n) := by
    by_cases hn : a ≤ n ∧ n ≤ max a b
    · have := hV n (Finset.mem_Icc.2 hn)
      exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset W.ι V.ι
        (by simpa using hW) _
    · exact IsFiniteLocallyConstantSheaf.of_isZero
        (G.map_isZero (hPz n (by omega)))
  have hP'f (n : ℤ) : ObjectProperty.flat (P'.X n) :=
    Functor.PreservesFlat.flat_obj (F := G) (hPflat n)
  have : CochainComplex.IsStrictlyGE P' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ G.map_isZero (hPz i (.inl hi))
  have : CochainComplex.IsStrictlyLE P' (max a b) := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ G.map_isZero (hPz i (.inr hi))
  -- the terms of `P'` are dualizable, with right duals their internal duals
  let _ (n : ℤ) : HasRightDual (P'.X n) :=
    { rightDual := (ihom (P'.X n)).obj (𝟙_ _)
      exact := letI := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (P'.X n) (hP'f n)
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_exactPairing_Q_obj_rightDual P' a (max a b)
  obtain ⟨ep⟩ := nonempty_exactPairing_swap (_root_.DerivedCategory.Q.obj P')
    (_root_.DerivedCategory.Q.obj (CochainComplex.rightDual P'))
  refine ⟨_, constructibleFiniteTor_Q_obj_of_flat Λ (CochainComplex.rightDual P') (-max a b) (-a)
    (fun n ↦ ?_) (fun n ↦ ?_), ⟨@exactPairingCongrRight _ _ _ _ _ _ ep
      ((leftDerivedUpperStarIsoMapDerivedCategory _ W.ι).app K ≪≫ G.mapDerivedCategory.mapIso e ≪≫
        G.mapDerivedCategoryFactors.app P)⟩⟩
  · -- the dual of a lisse flat sheaf is flat, being dualizable
    exact IsDualizable.flat ⟨@HasRightDual.mk _ _ _ _ (P'.X (-n))
      (exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (P'.X (-n)) (hP'f (-n)))⟩
  · -- and lisse
    have := isFiniteLocallyConstantSheaf_ihom_unit_of_flat (P'.X (-n)) (hP'f (-n))
    exact IsFiniteLocallyConstantSheaf.isConstructibleSheaf this

omit [Finite Λ] in
/-- On a nonempty noetherian scheme with a single point every constructible sheaf is finite
locally constant: it is so on a dense open, which is the whole scheme. -/
lemma isFiniteLocallyConstantSheaf_of_isConstructibleSheaf_of_subsingleton {X : Scheme.{u}}
    [IsNoetherian X] [Subsingleton X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] : IsFiniteLocallyConstantSheaf F := by
  obtain ⟨U, hU, hUl⟩ := IsConstructibleSheaf.exists_dense_open F
  by_cases hX : IsEmpty X
  · exact IsFiniteLocallyConstantSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  rw [not_isEmpty_iff] at hX
  have hU' : (U : Set X) = Set.univ := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact Set.eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx
  have := IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (𝟙 X) U.ι
    (by simp [hU']) F
  exact IsFiniteLocallyConstantSheaf.of_iso ((Etale.upperStarId _ X).app F)

/-- **Perfectness at a point**: on a nonempty noetherian scheme with a single point (for
instance the spectrum of a field), every object of `Dctf(X, Λ)` is dualizable. It is
represented by a bounded complex of flat constructible, hence lisse flat, sheaves, which are
dualizable (`AlgebraicGeometry.Etale.exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf`). This is
the geometric form of blueprint `lemma-perfect-complexes-geometric-point--8`: a finite-Tor point
complex is perfect. -/
theorem isDualizable_of_constructibleFiniteTor_of_subsingleton {X : Scheme.{u}} [IsNoetherian X]
    [Subsingleton X]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) : IsDualizable K := by
  obtain ⟨a, b, ⟨⟨hbc, -⟩, hta⟩⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  obtain ⟨P, ⟨hPz, hPflat⟩, hPc, ⟨e⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel
    Λ a (max a b) (le_max_left a b) K hbc).1
    (hasTorAmplitudeIn_of_torAmplitudeIn (hta.mono le_rfl (le_max_right a b)))
  have : CochainComplex.IsStrictlyGE P a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hPz i (.inl hi)
  have : CochainComplex.IsStrictlyLE P (max a b) := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hPz i (.inr hi)
  refine IsDualizable.of_iso e.symm (_root_.DerivedCategory.isDualizable_Q_obj P a (max a b)
    fun n ↦ ?_)
  have := hPc n
  have := isFiniteLocallyConstantSheaf_of_isConstructibleSheaf_of_subsingleton Λ (P.X n)
  exact ⟨@HasRightDual.mk _ _ _ _ ((ihom (P.X n)).obj (𝟙_ _))
    (letI := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf (P.X n) (hPflat n);
      BraidedCategory.exactPairing_swap _ _)⟩

end Etale

end AlgebraicGeometry
