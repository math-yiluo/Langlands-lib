/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Homology.ShortComplex.Linear
import WeilConjectures.Algebra.Homology.MinimalMatrixComplex
import WeilConjectures.Algebra.Homology.MatrixComplexTower
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Perfect complexes over the integral coefficient tower

Source: Weil conjectures blueprint, `lemma-perfect-complexes-over-oe`, statement (1), (2)
(blueprint: lemma-perfect-complexes-over-oe).

Positive levels are indexed by `n : ℕ`, with level `n` meaning exponent `n + 1`.
The isomorphisms of (1) are expressed by their adjoint universal arrows. For a bounded
finite free complex, ordinary quotient reduction computes derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Padic

/-- The ordinary quotient complex by a power of a scalar, constructed as a cokernel.
Cokernels of complexes of modules are computed degreewise, so this is the termwise quotient.
Source: blueprint `lemma-perfect-complexes-over-oe`, statement (2)
(blueprint: lemma-perfect-complexes-over-oe). -/
def scalarQuotient {A : Type u} [CommRing A]
    (t : A) (Q : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  cokernel (t ^ n • 𝟙 Q)

/-- The actual quotient transition, induced by the identity on the integral complex.
Source: blueprint `lemma-perfect-complexes-over-oe`, statement (2)
(blueprint: lemma-perfect-complexes-over-oe). -/
def scalarQuotientTransition {A : Type u} [CommRing A]
    (t : A) (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (m n : ℕ) (h : n ≤ m) : scalarQuotient t Q m ⟶ scalarQuotient t Q n :=
  cokernel.desc (t ^ m • 𝟙 Q) (cokernel.π (t ^ n • 𝟙 Q)) (by
    rw [← Nat.sub_add_cancel h, pow_add, mul_smul, Linear.smul_comp,
      cokernel.condition, smul_zero])

/-- Precomposition by an isomorphism preserves universal arrows.
Source: the scalar adjunction used in blueprint proof (1)
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem universal_precomp_iso
    {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {X X' : C} {Y : D} (e : X' ≅ X) (η : X ⟶ F.obj Y)
    (h : ∀ Z, Function.Bijective fun g : Y ⟶ Z ↦ η ≫ F.map g) :
    ∀ Z, Function.Bijective fun g : Y ⟶ Z ↦ (e.hom ≫ η) ≫ F.map g := by
  intro Z
  convert (e.symm.homFromEquiv (Z := F.obj Z)).bijective.comp (h Z) using 1
  ext g
  simp

/-- Changing the represented target by an isomorphism preserves its universal arrow.
Source: the scalar adjunction used in blueprint proof (1)
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem universal_postcomp_iso
    {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {X : C} {Y Y' : D} (η : X ⟶ F.obj Y) (e : Y ≅ Y')
    (h : ∀ Z, Function.Bijective fun g : Y ⟶ Z ↦ η ≫ F.map g) :
    ∀ Z, Function.Bijective fun g : Y' ⟶ Z ↦ (η ≫ F.map e.hom) ≫ F.map g := by
  intro Z
  convert (h Z).comp (e.symm.homFromEquiv (Z := Z)).bijective using 1
  ext g
  simp

/-- A comparison of universal arrows is an isomorphism.
Source: blueprint proof (1), uniqueness of derived scalar extension
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem universal_comparison_isIso
    {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {X : C} {Y Y' : D} (η : X ⟶ F.obj Y) (η' : X ⟶ F.obj Y')
    (h : ∀ Z, Function.Bijective fun g : Y ⟶ Z ↦ η ≫ F.map g)
    (h' : ∀ Z, Function.Bijective fun g : Y' ⟶ Z ↦ η' ≫ F.map g)
    (φ : Y ⟶ Y') (hφ : η ≫ F.map φ = η') : IsIso φ := by
  obtain ⟨ψ, hψ⟩ := (h' Y).2 η
  change η' ≫ F.map ψ = η at hψ
  refine ⟨⟨ψ, (h Y).1 ?_, (h' Y').1 ?_⟩⟩
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hφ]
    simp [hψ]
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hψ, hφ]
    simp

/-- Minimal finite free matrix representatives, with an independent localization universe.
Source: `MatrixComplex.exists_iso_Q_obj_of_isPerfect`; the same proof uses the recorded
minimal-complex theorem and the actual perfectness witness.
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem minimal_matrix_model {S : Type u} [CommRing S] [IsLocalRing S]
    [HasDerivedCategory.{v} (ModuleCat.{u} S)]
    {K : DerivedCategory (ModuleCat.{u} S)} (hK : DerivedCategory.IsPerfectRingComplex K) :
    ∃ (r : ℤ → ℕ) (lo hi : ℤ) (M : MatrixComplex r S),
      (∀ i, i < lo → r i = 0) ∧ (∀ i, hi < i → r i = 0) ∧ M.IsMinimal ∧
      Nonempty (DerivedCategory.Q.obj M.complex ≅ K) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  have (i : ℤ) : Module.Finite S (P.X i) := (hP i).2
  have (i : ℤ) : Module.Projective S (P.X i) := (hP i).1
  have (i : ℤ) : Module.Free S (P.X i) := Module.free_of_flat_of_isLocalRing
  obtain ⟨N, hN, hNa, hNb, hNfree, hNfin, ⟨h⟩⟩ :=
    CochainComplex.exists_homotopyEquiv_isMinimal P a b
  let eb (i : ℤ) : N.X i ≃ₗ[S] (Fin (Module.finrank S (N.X i)) → S) :=
    haveI := hNfree i
    haveI := hNfin i
    (Module.finBasis S (N.X i)).equivFun
  refine ⟨_, a, b, MatrixComplex.ofLinearEquiv N eb, fun i hi ↦ ?_, fun i hi ↦ ?_,
    MatrixComplex.IsMinimal.ofLinearEquiv hN eb, ⟨?_⟩⟩
  · have := ModuleCat.isZero_iff_subsingleton.1 (N.isZero_of_isStrictlyGE a i hi)
    exact Module.finrank_zero_of_subsingleton
  · have := ModuleCat.isZero_iff_subsingleton.1 (N.isZero_of_isStrictlyLE b i hi)
    exact Module.finrank_zero_of_subsingleton
  · have : IsIso (DerivedCategory.Q.map h.inv) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    exact DerivedCategory.Q.mapIso (MatrixComplex.isoOfLinearEquiv N eb).symm ≪≫
      asIso (DerivedCategory.Q.map h.inv) ≪≫ e.symm

/-- Derived isomorphisms between minimal matrix models have invertible chain representatives.
Source: `MatrixComplex.exists_isIso_Q_map_eq`, using K-projective representatives and
`CochainComplex.isIso_of_quasiIso_of_isMinimal` without identifying universes.
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem minimal_matrix_comparison {S : Type u} [CommRing S] [IsLocalRing S]
    [HasDerivedCategory.{v} (ModuleCat.{u} S)] {r r' : ℤ → ℕ}
    {M : MatrixComplex r S} {N : MatrixComplex r' S}
    (hM : M.IsMinimal) (hN : N.IsMinimal) (hi hi' : ℤ)
    (hMhi : ∀ i, hi < i → r i = 0) (hNhi : ∀ i, hi' < i → r' i = 0)
    (ψ : DerivedCategory.Q.obj M.complex ⟶ DerivedCategory.Q.obj N.complex) [IsIso ψ] :
    ∃ g : M.complex ⟶ N.complex, IsIso g ∧ DerivedCategory.Q.map g = ψ := by
  have := M.isStrictlyLE_complex hi hMhi
  have := N.isStrictlyLE_complex hi' hNhi
  obtain ⟨g, rfl⟩ := DerivedCategory.Q_map_surjective_of_projective M.complex N.complex hi ψ
  have : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 inferInstance
  exact ⟨g, CochainComplex.isIso_of_quasiIso_of_isMinimal g hi hi' hM.complex hN.complex, rfl⟩

/-- Ordinary reduction of bounded free matrix complexes computes derived reduction.
Source: `MatrixComplex.isDerivedBaseChange_reduction`; `ReductionDatum.bijective_comp_map`
allows the localization universe to be independent of the coefficient universe.
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem matrix_reduction_universal {S S' : Type u} [CommRing S] [CommRing S']
    [HasDerivedCategory.{v} (ModuleCat.{u} S)]
    [HasDerivedCategory.{v} (ModuleCat.{u} S')] {r : ℤ → ℕ}
    (M : MatrixComplex r S) (φ : S →+* S') (hφ : Function.Surjective φ) {a : S}
    (ha : RingHom.ker φ = Ideal.span {a}) (lo hi : ℤ)
    (hlo : ∀ i, i < lo → r i = 0) (hhi : ∀ i, hi < i → r i = 0)
    (N : MatrixComplex r S') (h : ∀ i, (M.d i).map φ = N.d i) :
    ∀ Z : DerivedCategory (ModuleCat.{u} S'), Function.Bijective fun g :
      DerivedCategory.Q.obj N.complex ⟶ Z ↦
      (DerivedCategory.Q.map (M.reduction φ N h) ≫
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app N.complex) ≫
          (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map g := by
  have := ModuleCat.restrictScalars_full_of_surjective.{u} φ hφ
  have := M.isStrictlyGE_complex lo hlo
  have := M.isStrictlyLE_complex hi hhi
  let D := ModuleCat.reductionDatum φ hφ a ha
  have h₀ := D.bijective_comp_map M.complex
    (CochainComplex.kFlat_of_bounded_of_flat M.complex lo hi fun n ↦
      (ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat S (Fin (r n) → S))))
  let δ := D.descComplex (M.reduction φ N h)
  have : IsIso δ := by
    have (i : ℤ) : IsIso (δ.f i) := MatrixComplex.isIso_reductionDatum_desc φ hφ ha _
      (MatrixComplex.reductionHom_surjective φ hφ (r i))
      (MatrixComplex.exists_eq_smul_of_reductionHom_eq_zero φ ha)
    exact HomologicalComplex.Hom.isIso_of_components _
  convert universal_postcomp_iso (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory _
    (asIso (DerivedCategory.Q.map δ)) h₀ using 1
  rw [← D.complexMap_comp_descComplex (M.reduction φ N h), Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryFactors_inv_naturality, asIso_hom, Category.assoc]

/-- Internal record of a chosen minimal matrix model of one tower level.
Source: blueprint proof (1), minimal finite free representatives
(blueprint: lemma-perfect-complexes-over-oe). -/
private structure ScalarLevelModel {A : ℕ → Type u} [∀ n, CommRing (A n)]
    [∀ n, HasDerivedCategory.{v} (ModuleCat.{u} (A n))]
    (M : ∀ n, DerivedCategory (ModuleCat.{u} (A n))) (r : ℤ → ℕ) (n : ℕ)
    [IsLocalRing (A n)] where
  matrix : MatrixComplex r (A n)
  minimal : matrix.IsMinimal
  iso : DerivedCategory.Q.obj matrix.complex ≅ M n

/-- Adjacent matrix models whose actual reduction represents the specified transition.
Source: blueprint proof (1), changing bases at successive levels
(blueprint: lemma-perfect-complexes-over-oe). -/
private def ScalarLevelModel.IsSucc {A : ℕ → Type u} [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)] [∀ n, HasDerivedCategory.{v} (ModuleCat.{u} (A n))]
    {M : ∀ n, DerivedCategory (ModuleCat.{u} (A n))}
    (ρ : ∀ n, A (n + 1) →+* A n)
    (f : ∀ n, M (n + 1) ⟶ (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.obj (M n))
    {r : ℤ → ℕ} {n : ℕ} (x : ScalarLevelModel M r n)
    (y : ScalarLevelModel M r (n + 1)) : Prop :=
  ∃ h : ∀ i, (y.matrix.d i).map (ρ n) = x.matrix.d i,
    DerivedCategory.Q.map (y.matrix.reduction (ρ n) x.matrix h) ≫
      (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategoryFactors.inv.app x.matrix.complex ≫
        (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.map x.iso.hom = y.iso.hom ≫ f n

/-- Extend a matrix model by lifting an invertible comparison and conjugating.
Source: `ModuleCat.NormalizedPerfectTower.LevelModel.exists_isSucc`; its matrix argument
works unchanged with the universe-general universal arrows above.
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem scalar_level_succ {R : Type u} [CommRing R]
    {A : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, IsLocalRing (A n)]
    [∀ n, HasDerivedCategory.{v} (ModuleCat.{u} (A n))]
    (π : ∀ n, R →+* A n) (ρ : ∀ n, A (n + 1) →+* A n)
    (hρ : ∀ n, π n = (ρ n).comp (π (n + 1)))
    (hπ : ∀ n, Function.Surjective (π n)) {t : R}
    (hker : ∀ n, RingHom.ker (π n) = Ideal.span {t ^ (n + 1)})
    (M : ∀ n, DerivedCategory (ModuleCat.{u} (A n)))
    (f : ∀ n, M (n + 1) ⟶ (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.obj (M n))
    (hM : ∀ n, DerivedCategory.IsPerfectRingComplex (M n))
    (hf : ∀ n N, Function.Bijective fun g : M n ⟶ N ↦
      f n ≫ (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.map g)
    {r : ℤ → ℕ} {hi : ℤ} (hhi : ∀ i, hi < i → r i = 0) {n : ℕ}
    (x : ScalarLevelModel M r n) : ∃ y : ScalarLevelModel M r (n + 1),
      x.IsSucc ρ f y := by
  obtain ⟨r', lo', hi', M', hlo', hhi', hM', ⟨e'⟩⟩ := minimal_matrix_model (hM (n + 1))
  have hρs : Function.Surjective (ρ n) := Function.Surjective.of_comp (g := π (n + 1)) (by
    rw [← RingHom.coe_comp, ← hρ n]
    exact hπ n)
  have := IsLocalHom.of_surjective (ρ n) hρs
  have hη := matrix_reduction_universal M' (ρ n) hρs
    (RingHom.ker_eq_span_singleton_of_comp (hπ (n + 1)) (ρ n) ((hρ n) ▸ hker n))
    lo' hi' hlo' hhi' (M'.map (ρ n)) fun _ ↦ rfl
  obtain ⟨θ, hθ⟩ := (hη (M n)).2 (e'.hom ≫ f n)
  have : IsIso θ := universal_comparison_isIso _ _ _ hη
    (universal_precomp_iso _ e' (f n) (hf n)) θ hθ
  obtain ⟨g, hg, hgθ⟩ := minimal_matrix_comparison (hM'.map (ρ n)) x.minimal hi' hi
    hhi' hhi (θ ≫ x.iso.inv)
  obtain rfl : r' = r := funext (MatrixComplex.rank_eq_of_isIso g)
  choose b hb hbu using fun i ↦ MatrixComplex.exists_map_eq_isUnit_det (ρ n) hρs
    (MatrixComplex.toMatrix g i) (MatrixComplex.isUnit_det_toMatrix g i)
  refine ⟨⟨M'.conj b hbu, hM'.conj b hbu,
    (asIso (DerivedCategory.Q.map (M'.conjHom b hbu))).symm ≪≫ e'⟩,
    M'.map_conj_d b hbu (ρ n) x.matrix _ hb (MatrixComplex.toMatrix_comm g), ?_⟩
  rw [← cancel_epi (DerivedCategory.Q.map (M'.conjHom b hbu))]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← hθ, ← Functor.map_comp_assoc, MatrixComplex.reduction_naturality (ρ n) (fun _ ↦ rfl) _
    _ g fun i ↦ by rw [MatrixComplex.toMatrix_conjHom, hb], Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_inv_naturality_assoc, ← Functor.map_comp, hgθ,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc]

/-- The canonical associativity comparison for the derived restriction functors.
Source: `ModuleCat.derivedRestrictScalarsCompIso`, with independent localization universe
(blueprint: lemma-perfect-complexes-over-oe). -/
private def scalarRestrictionCompIso {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [HasDerivedCategory.{v} (ModuleCat.{u} R)] [HasDerivedCategory.{v} (ModuleCat.{u} S)]
    [HasDerivedCategory.{v} (ModuleCat.{u} T)] {f : R →+* S} {g : S →+* T} {gf : R →+* T}
    (hgf : gf = g.comp f) :
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} gf).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g gf hgf).symm

/-- The restriction comparison identifies the two images of an actual composite chain map.
Source: `ModuleCat.Q_map_restrictScalars_comp`, with independent localization universe
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem scalar_restriction_comp {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    [HasDerivedCategory.{v} (ModuleCat.{u} S)] [HasDerivedCategory.{v} (ModuleCat.{u} T)]
    {f : R →+* S} {g : S →+* T} {gf : R →+* T} (hgf : gf = g.comp f)
    {K : CochainComplex (ModuleCat.{u} S) ℤ} {L : CochainComplex (ModuleCat.{u} T) ℤ}
    (χ : K ⟶ ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex _).obj L) :
    DerivedCategory.Q.map (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex _).map χ ≫
        ModuleCat.restrictScalarsCompComplexMap hgf L) ≫
        (ModuleCat.restrictScalars.{u} gf).mapDerivedCategoryFactors.inv.app L =
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app K ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (DerivedCategory.Q.map χ ≫
          (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app L) ≫
        (scalarRestrictionCompIso hgf).hom.app (DerivedCategory.Q.obj L) := by
  rw [← cancel_mono ((ModuleCat.restrictScalars.{u} gf).mapDerivedCategoryFactors.hom.app L),
    Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id, Category.assoc]
  have h₁ : (scalarRestrictionCompIso hgf).hom.app (DerivedCategory.Q.obj L) ≫
      (ModuleCat.restrictScalars.{u} gf).mapDerivedCategoryFactors.hom.app L =
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.hom.app L) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex _).obj L) ≫
        DerivedCategory.Q.map (ModuleCat.restrictScalarsCompComplexMap hgf L) := by
    simp only [scalarRestrictionCompIso, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac,
      ← Functor.mapDerivedCategoryCompIso_fac (ModuleCat.restrictScalars g)
        (ModuleCat.restrictScalars f) L]
    simp only [Functor.comp_obj, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
    have h₂ : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.restrictScalars.{u} g ⋙ ModuleCat.restrictScalars.{u} f))
          (.up ℤ)).hom.app L ≫
          (NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp' f g gf hgf).inv
            (.up ℤ)).app L = ModuleCat.restrictScalarsCompComplexMap hgf L := by
      ext i x
      rfl
    rw [← Functor.map_comp, h₂]
  rw [h₁, Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
      ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app L),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]

/-- Reconstruct the bounded free model by strictifying finite levels and taking matrix limits.
Source: blueprint proof (1), implemented with the adopted minimal-matrix and tower-limit APIs.
All intermediate choices have proved existence; the integral differential is constructed entrywise.
(blueprint: lemma-perfect-complexes-over-oe). -/
private theorem scalar_tower_from_complete {R : Type u} [CommRing R]
    {A : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, IsLocalRing (A n)]
    [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    [∀ n, HasDerivedCategory.{v} (ModuleCat.{u} (A n))]
    (π : ∀ n, R →+* A n) (ρ : ∀ n, A (n + 1) →+* A n)
    (hρ : ∀ n, π n = (ρ n).comp (π (n + 1)))
    (hπ : ∀ n, Function.Surjective (π n)) {t : R}
    (hker : ∀ n, RingHom.ker (π n) = Ideal.span {t ^ (n + 1)})
    (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) →
      ∃ r : R, ∀ n, π n r = x n)
    (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)
    (M : ∀ n, DerivedCategory (ModuleCat.{u} (A n)))
    (f : ∀ n, M (n + 1) ⟶ (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.obj (M n))
    (hM : ∀ n, DerivedCategory.IsPerfectRingComplex (M n))
    (hf : ∀ n N, Function.Bijective fun g : M n ⟶ N ↦
      f n ≫ (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategory.map g) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ∃ p : ∀ n, DerivedCategory.Q.obj P ⟶
          (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategory.obj (M n),
        (∀ n N, Function.Bijective fun g : M n ⟶ N ↦
          p n ≫ (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategory.map g) ∧
        (∀ n, p (n + 1) ≫
          (ModuleCat.restrictScalars.{u} (π (n + 1))).mapDerivedCategory.map (f n) ≫
            (scalarRestrictionCompIso (hρ n)).hom.app (M n) = p n) := by
  classical
  obtain ⟨r, lo, hi, M₀, hlo, hhi, hM₀, ⟨e₀⟩⟩ := minimal_matrix_model (hM 0)
  let x₀ : ScalarLevelModel M r 0 := ⟨M₀, hM₀, e₀⟩
  have hnext {n : ℕ} (x : ScalarLevelModel M r n) :
      ∃ y : ScalarLevelModel M r (n + 1), x.IsSucc ρ f y :=
    scalar_level_succ π ρ hρ hπ hker M f hM hf hhi x
  let level : ∀ n, ScalarLevelModel M r n :=
    fun n ↦ Nat.rec x₀ (fun _ x ↦ (hnext x).choose) n
  have hs (n : ℕ) : (level n).IsSucc ρ f (level (n + 1)) :=
    (hnext (level n)).choose_spec
  let L := MatrixComplex.towerLim (fun n ↦ (level n).matrix) (fun n ↦ (hs n).1)
    hcomplete hsep
  have hL := MatrixComplex.map_towerLim_d (fun n ↦ (level n).matrix)
    (fun n ↦ (hs n).1) hcomplete hsep
  let p (n : ℕ) := DerivedCategory.Q.map (L.reduction (π n) (level n).matrix (hL n)) ≫
    (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategoryFactors.inv.app
      (level n).matrix.complex ≫
    (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategory.map (level n).iso.hom
  refine ⟨L.complex, lo, hi, L.isStrictlyGE_complex lo hlo,
    L.isStrictlyLE_complex hi hhi, fun i ↦ ⟨inferInstance, inferInstance⟩, p, ?_, ?_⟩
  · intro n
    simpa only [p, Category.assoc] using universal_postcomp_iso _ _ (level n).iso
      (matrix_reduction_universal L (π n) (hπ n) (hker n) lo hi hlo hhi
        (level n).matrix (hL n))
  · intro n
    have hnat := (scalarRestrictionCompIso (hρ n)).hom.naturality (level n).iso.hom
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    dsimp only [p]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← (hs n).2]
    simp only [Functor.map_comp, Category.assoc]
    rw [hnat]
    have hc := scalar_restriction_comp (hρ n)
      ((level (n + 1)).matrix.reduction (ρ n) (level n).matrix (hs n).1)
    rw [← Functor.map_comp_assoc, ← reassoc_of% hc, ← Functor.map_comp_assoc]
    have hchain := MatrixComplex.reduction_comp_towerFunctor_map hρ
      (fun n ↦ (hs n).1) L hL n
    rw [MatrixComplex.towerFunctor_map_succ] at hchain
    rw [← Category.assoc, hchain]
    simp only [Category.assoc]

section Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [HasDerivedCategory.{v} (ModuleCat.{u} (coefficientExtensionIntegers l E))]
  [∀ n : ℕ, HasDerivedCategory.{v} (ModuleCat.{u} (coefficientExtensionRing l E n))]

/-- A compatible tower of perfect complexes over the positive coefficient quotients is
represented by one bounded finite free integral complex. The maps in the conclusion are the
universal arrows for the derived reductions, and the displayed equation is their compatibility
with the given transition maps.

Source: current blueprint, `lemma-perfect-complexes-over-oe`, statement and proof (1)
(blueprint: lemma-perfect-complexes-over-oe).

Proof: choose minimal finite free representatives over the local quotient rings. Their
reductions are homotopy equivalent; reducing a homotopy equivalence modulo the maximal ideal
makes its matrices invertible. Lift these matrices and conjugate inductively, then lift the
compatible matrix entries through the complete coefficient ring. -/
theorem integral_scalar_tower_lift
    (M : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (coefficientExtensionRing l E (n + 1))))
    (f : ∀ n : ℕ, M (n + 1) ⟶
      ((ModuleCat.restrictScalars.{u}
        (coefficientExtensionTransition l E (n + 1))).mapDerivedCategory).obj (M n))
    (hM : ∀ n : ℕ, DerivedCategory.IsPerfectRingComplex (M n))
    (hf : ∀ (n : ℕ)
      (N : DerivedCategory (ModuleCat.{u} (coefficientExtensionRing l E (n + 1)))),
      Function.Bijective fun g : M n ⟶ N ↦ f n ≫
        ((ModuleCat.restrictScalars.{u}
          (coefficientExtensionTransition l E (n + 1))).mapDerivedCategory).map g) :
    ∃ (P : CochainComplex (ModuleCat.{u} (coefficientExtensionIntegers l E)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (coefficientExtensionIntegers l E) (P.X i) ∧
        Module.Finite (coefficientExtensionIntegers l E) (P.X i)) ∧
      ∃ p : ∀ n : ℕ, DerivedCategory.Q.obj P ⟶
        (ModuleCat.restrictScalars.{u}
          (Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)))).mapDerivedCategory.obj (M n),
        (∀ (n : ℕ)
          (N : DerivedCategory (ModuleCat.{u} (coefficientExtensionRing l E (n + 1)))),
          Function.Bijective fun g : M n ⟶ N ↦ p n ≫
            (ModuleCat.restrictScalars.{u}
              (Ideal.Quotient.mk
                (coefficientExtensionIdeal l E (n + 1)))).mapDerivedCategory.map g) ∧
        (∀ n : ℕ, p (n + 1) ≫
          (ModuleCat.restrictScalars.{u}
            (Ideal.Quotient.mk
              (coefficientExtensionIdeal l E (n + 1 + 1)))).mapDerivedCategory.map
            (f n) ≫
          (Functor.mapDerivedCategoryCompIso _ _ ≪≫
            Functor.mapDerivedCategoryNatIso
              (ModuleCat.restrictScalarsComp'
                (Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1 + 1)))
                (coefficientExtensionTransition l E (n + 1))
                (Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)))
                (by ext x; rfl)).symm).hom.app (M n) = p n) := by
  classical
  let A := coefficientExtensionIntegers l E
  let B := fun n : ℕ ↦ coefficientExtensionRing l E (n + 1)
  let π := fun n : ℕ ↦ Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1))
  let ρ := fun n : ℕ ↦ coefficientExtensionTransition l E (n + 1)
  let t : A := coefficientExtensionUniformizer l E
  have hcoeff := (coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsLocalRing A := hcoeff.2.2.2.1
  have hgen : Ideal.span ({t} : Set A) = coefficientExtensionMaximalIdeal l E :=
    hcoeff.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hproper : ∀ n : ℕ, coefficientExtensionIdeal l E (n + 1) ≠ ⊤ := by
    intro n
    change Ideal.span ({t} : Set A) ^ (n + 1) ≠ ⊤
    intro h
    have hle : Ideal.span ({t} : Set A) ^ (n + 1) ≤
        coefficientExtensionMaximalIdeal l E :=
      (Ideal.pow_le_self (by omega)).trans hgen.le
    rw [h] at hle
    exact hcoeff.2.2.2.2.1.ne_top (top_le_iff.mp hle)
  have (n : ℕ) : Nontrivial (B n) := Ideal.Quotient.nontrivial_iff.mpr (hproper n)
  have (n : ℕ) : IsLocalRing (B n) :=
    IsLocalRing.of_surjective' (π n) Ideal.Quotient.mk_surjective
  have hπ (n : ℕ) : Function.Surjective (π n) := Ideal.Quotient.mk_surjective
  have hker (n : ℕ) : RingHom.ker (π n) = Ideal.span {t ^ (n + 1)} := by
    rw [Ideal.mk_ker]
    exact Ideal.span_singleton_pow _ _
  have hρ (n : ℕ) : π n = (ρ n).comp (π (n + 1)) := by ext x; rfl
  obtain ⟨e, he, _⟩ := (coefficientExtension_integers_profinite_tower.{u, u} l E).1
  have hcomplete (x : ∀ n, B n) (hx : ∀ n, ρ n (x (n + 1)) = x n) :
      ∃ r : A, ∀ n, π n r = x n := by
    have hx' : x ∈ coefficientExtensionPositiveLimit l E := by
      simp only [coefficientExtensionPositiveLimit, Subring.mem_iInf, RingHom.mem_eqLocus]
      exact hx
    refine ⟨e.symm ⟨x, hx'⟩, fun n ↦ ?_⟩
    rw [← he]
    exact congrArg (fun z ↦ z.val n) (e.apply_symm_apply ⟨x, hx'⟩)
  have hsep (r : A) (hr : ∀ n, π n r = 0) : r = 0 := by
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he r n, he 0 n]
    exact (hr n).trans (map_zero _).symm
  exact scalar_tower_from_complete π ρ hρ hπ hker hcomplete hsep M f hM hf

end Coefficients

/-- Scalar multiplication on homology, via the linear short-complex homology functor.
Source: Mathlib `ShortComplex.homologyMap_smul`; the scalar action used in blueprint
`lemma-perfect-complexes-over-oe`, proof (2) (blueprint: lemma-perfect-complexes-over-oe). -/
private theorem homologyMap_scalar_id {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 C) i = r • 𝟙 (C.homology i) := by
  change ShortComplex.homologyMap (r • 𝟙 (C.sc i)) = r • 𝟙 (C.homology i)
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- The images in cohomology of a bounded finite free integral complex stabilize at a
uniform torsion rate for the actual quotient transitions.

Source: current blueprint, `lemma-perfect-complexes-over-oe`, statement and proof (2)
(blueprint: lemma-perfect-complexes-over-oe).

Proof: the regular quotient exact sequence identifies the quotient cohomology with integral
cohomology and the next cohomology's uniformizer torsion. The transition on the latter is
multiplication by the intervening power, hence vanishes after the torsion exponent. -/
theorem integral_scalar_cohomology_images
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Q : CochainComplex (ModuleCat.{u} (coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : Q.IsStrictlyGE a) (hb : Q.IsStrictlyLE b)
    (hQ : ∀ i : ℤ, Module.Free (coefficientExtensionIntegers l E) (Q.X i) ∧
      Module.Finite (coefficientExtensionIntegers l E) (Q.X i))
    (q : ℤ) (e : ℕ)
    (he : ∀ x ∈ Submodule.torsion (coefficientExtensionIntegers l E) (Q.homology (q + 1)),
      coefficientExtensionUniformizer l E ^ e • x = 0)
    (m n : ℕ) (hn : 1 ≤ n) (hm : n + e ≤ m) :
    Set.range (HomologicalComplex.homologyMap
      (scalarQuotientTransition (coefficientExtensionUniformizer l E) Q m n
        ((Nat.le_add_right n e).trans hm)) q) =
      Set.range (HomologicalComplex.homologyMap
        (cokernel.π (coefficientExtensionUniformizer l E ^ n • 𝟙 Q)) q) := by
  have _ := ha
  have _ := hb
  have _ := hn
  let A := coefficientExtensionIntegers l E
  let t : A := coefficientExtensionUniformizer l E
  have hcoeff := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({t} : Set A) = coefficientExtensionMaximalIdeal l E :=
    hcoeff.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have ht : t ≠ 0 := by
    intro h
    have hm0 : coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
      hcoeff.2.2.2.2.2.2.2.2.2.1
    apply hm0
    rw [← hgen, h, Ideal.span_singleton_zero]
  have instFree (i : ℤ) : Module.Free A (Q.X i) := (hQ i).1
  have hmono (k : ℕ) : Mono (t ^ k • 𝟙 Q) := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    apply (ModuleCat.mono_iff_injective _).2
    change Function.Injective (fun x : Q.X i ↦ t ^ k • x)
    exact smul_right_injective (Q.X i) (pow_ne_zero k ht)
  let S (k : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
    ShortComplex.mk (t ^ k • 𝟙 Q) (cokernel.π (t ^ k • 𝟙 Q))
      (cokernel.condition _)
  have hS (k : ℕ) : (S k).ShortExact := by
    have := hmono k
    exact { exact := ShortComplex.exact_cokernel _ }
  have hnm : n ≤ m := (Nat.le_add_right n e).trans hm
  let r := scalarQuotientTransition t Q m n hnm
  have hπ : cokernel.π (t ^ m • 𝟙 Q) ≫ r = cokernel.π (t ^ n • 𝟙 Q) := by
    dsimp [r, scalarQuotientTransition]
    exact cokernel.π_desc _ _ _
  let φ : S m ⟶ S n :=
    { τ₁ := t ^ (m - n) • 𝟙 Q
      τ₂ := 𝟙 Q
      τ₃ := r
      comm₁₂ := by
        dsimp [S]
        simp only [Category.comp_id, Linear.comp_smul, smul_smul, ← pow_add,
          Nat.add_sub_of_le hnm]
      comm₂₃ := by simpa [S] using hπ.symm }
  let δ (k : ℕ) := (hS k).δ q (q + 1) (by simp)
  have hδ (x : (scalarQuotient t Q m).homology q) :
      t ^ m • δ m x = 0 := by
    have hx := congrArg (fun f => f x) ((hS m).δ_comp q (q + 1) (by simp))
    change HomologicalComplex.homologyMap (t ^ m • 𝟙 Q) (q + 1) (δ m x) = 0 at hx
    rw [homologyMap_scalar_id] at hx
    exact hx
  have htransition (x : (scalarQuotient t Q m).homology q) :
      δ n (HomologicalComplex.homologyMap r q x) = t ^ (m - n) • δ m x := by
    have hx := congrArg (fun f => f x)
      (HomologicalComplex.HomologySequence.δ_naturality φ (hS m) (hS n)
        q (q + 1) (by simp))
    change HomologicalComplex.homologyMap (t ^ (m - n) • 𝟙 Q) (q + 1) (δ m x) =
      δ n (HomologicalComplex.homologyMap r q x) at hx
    rw [homologyMap_scalar_id] at hx
    exact hx.symm
  have hzero (x : (scalarQuotient t Q m).homology q) :
      δ n (HomologicalComplex.homologyMap r q x) = 0 := by
    rw [htransition]
    have hx : δ m x ∈ Submodule.torsion A (Q.homology (q + 1)) := by
      apply (Submodule.mem_torsion_iff _).2
      exact ⟨⟨t ^ m, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero m ht)⟩, hδ x⟩
    have hexp : e ≤ m - n := by omega
    rw [← Nat.sub_add_cancel hexp, pow_add, mul_smul, he _ hx, smul_zero]
  change Set.range (HomologicalComplex.homologyMap r q) =
    Set.range (HomologicalComplex.homologyMap (cokernel.π (t ^ n • 𝟙 Q)) q)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (ShortComplex.moduleCat_exact_iff _).1
      ((hS n).homology_exact₃ q (q + 1) (by simp)) _ (hzero x)
  · rintro ⟨x, rfl⟩
    refine ⟨HomologicalComplex.homologyMap (cokernel.π (t ^ m • 𝟙 Q)) q x, ?_⟩
    change (HomologicalComplex.homologyMap (cokernel.π (t ^ m • 𝟙 Q)) q ≫
      HomologicalComplex.homologyMap r q) x = _
    rw [← HomologicalComplex.homologyMap_comp, hπ]
    rfl

end Padic
