/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Kummer covers in the pro-étale site

Let `A` be a ring, `f ∈ A` a unit and `r` a natural number invertible in `A`. The Kummer tower
of `f` is the sequence of étale `A`-algebras `A[T]/(T^{rⁿ} - f)`, with transition maps
`T ↦ T^{r^{m - n}}`; its colimit `A[f^{1/r^∞}]` (`AlgebraicGeometry.ProEtale.kummerRing`) is
ind-étale, hence weakly étale, and integral and faithful over `A`, hence surjective on spectra.

For an affine open `U` of a scheme `X` and `f ∈ Γ(X, U)ˣ`, this gives an object
`AlgebraicGeometry.Scheme.ProEt.kummerCover` of `X_proét` with underlying scheme
`Spec Γ(X, U)[f^{1/r^∞}]` and image `U`. Finitely many of these, over an affine open cover of
`X`, cover the terminal object of `X_proét`.

If `X` is integral and its function field `K` contains the `rᵐ`-th roots of unity, then for every
morphism `g` from the geometric generic point to a Kummer cover (or to an object over a Kummer
cover) and every `σ ∈ Gal(Kˢᵉᵖ/K)` fixing `g`, `σ` fixes every `rᵐ`-th root of `f` in `Kˢᵉᵖ`.

## Main definitions

- `AlgebraicGeometry.ProEtale.kummerRing`: the ring `A[f^{1/r^∞}]`, with the compatible roots
  `AlgebraicGeometry.ProEtale.kummerRoot f r m` of `f` of order `rᵐ`.
- `AlgebraicGeometry.Scheme.ProEt.kummerCover`: `Spec Γ(X, U)[f^{1/r^∞}] ⟶ U ⟶ X` in `X_proét`.

## Main statements

- `AlgebraicGeometry.ProEtale.indEtale_kummerRing`.
- `AlgebraicGeometry.ProEtale.surjective_comap_algebraMap_kummerRing`.
- `AlgebraicGeometry.Scheme.ProEt.range_kummerCover_hom`: the image of a Kummer cover is `U`.
- `AlgebraicGeometry.Scheme.ProEt.ofArrows_kummerCover_mem_topology`: Kummer covers over a
  finite affine open cover of `X` cover the terminal object of `X_proét`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut_apply_eq_of_comp_kummerCover`: the Galois
  elements fixing a morphism from the geometric generic point to a Kummer cover fix the roots
  of `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry

namespace ProEtale

section Ring

variable {A : Type u} [CommRing A] (f : A) (r : ℕ)

/-- The `n`-th stage `A[T]/(T^{rⁿ} - f)` of the Kummer tower of `f`. -/
abbrev KummerStage (n : ℕ) : Type u :=
  AdjoinRoot (X ^ (r ^ n) - C f : A[X])

lemma kummerStage_root_pow (n : ℕ) :
    AdjoinRoot.root (X ^ (r ^ n) - C f) ^ (r ^ n) = algebraMap A (KummerStage f r n) f := by
  have h := AdjoinRoot.eval₂_root (X ^ (r ^ n) - C f)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

/-- The transition map `A[T]/(T^{rⁿ} - f) → A[T]/(T^{rᵐ} - f)`, `T ↦ T^{r^{m - n}}`, of the
Kummer tower, for `n ≤ m`. -/
noncomputable def kummerStageMap {n m : ℕ} (h : n ≤ m) :
    KummerStage f r n →ₐ[A] KummerStage f r m :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.root _ ^ r ^ (m - n)) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← pow_mul, ← pow_add, Nat.sub_add_cancel h,
      kummerStage_root_pow, sub_eq_zero]
    rfl)

@[simp]
lemma kummerStageMap_root {n m : ℕ} (h : n ≤ m) :
    kummerStageMap f r h (AdjoinRoot.root _) = AdjoinRoot.root _ ^ r ^ (m - n) :=
  AdjoinRoot.liftAlgHom_root ..

lemma kummerStageMap_refl {n : ℕ} (h : n ≤ n) : kummerStageMap f r h = AlgHom.id A _ :=
  AdjoinRoot.algHom_ext (by simp)

lemma kummerStageMap_comp {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    (kummerStageMap f r h₂).comp (kummerStageMap f r h₁) = kummerStageMap f r (h₁.trans h₂) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, kummerStageMap_root, map_pow, kummerStageMap_root, kummerStageMap_root,
    ← pow_mul, ← pow_add, Nat.sub_add_sub_cancel h₂ h₁]

/-- The Kummer tower `n ↦ A[T]/(T^{rⁿ} - f)` of `f`, indexed by `ULift ℕ` so that it is a
`u`-small diagram. -/
@[simps]
noncomputable def kummerDiagram : ULift.{u} ℕ ⥤ CommRingCat.{u} where
  obj n := .of (KummerStage f r n.down)
  map h := CommRingCat.ofHom (kummerStageMap f r (ULift.down_le.mpr (leOfHom h))).toRingHom
  map_id n := by
    rw [kummerStageMap_refl]
    rfl
  map_comp h₁ h₂ := by
    rw [← kummerStageMap_comp f r (ULift.down_le.mpr (leOfHom h₁)) (ULift.down_le.mpr (leOfHom h₂))]
    rfl

/-- The ring `A[f^{1/r^∞}] = colim_n A[T]/(T^{rⁿ} - f)`. -/
noncomputable def kummerRing : CommRingCat.{u} :=
  colimit (kummerDiagram f r)

/-- The colimit inclusion `A[T]/(T^{rⁿ} - f) → A[f^{1/r^∞}]`. -/
noncomputable def kummerRingι (n : ℕ) : KummerStage f r n →+* kummerRing f r :=
  (colimit.ι (kummerDiagram f r) ⟨n⟩).hom

lemma kummerRingι_map {n m : ℕ} (h : n ≤ m) (x : KummerStage f r n) :
    kummerRingι f r m (kummerStageMap f r h x) = kummerRingι f r n x :=
  ConcreteCategory.congr_hom (colimit.w (kummerDiagram f r) (homOfLE (ULift.down_le.mp h))) x

noncomputable instance : Algebra A (kummerRing f r) :=
  ((kummerRingι f r 0).comp (algebraMap A _)).toAlgebra

lemma kummerRingι_algebraMap (n : ℕ) (a : A) :
    kummerRingι f r n (algebraMap A _ a) = algebraMap A (kummerRing f r) a := by
  rw [← (kummerStageMap f r (Nat.zero_le n)).commutes, kummerRingι_map]
  rfl

lemma kummerRingι_comp_algebraMap (n : ℕ) :
    (kummerRingι f r n).comp (algebraMap A _) = algebraMap A (kummerRing f r) :=
  RingHom.ext (kummerRingι_algebraMap f r n)

/-- The root `f^{1/rᵐ}` of `f` in `A[f^{1/r^∞}]`. -/
noncomputable def kummerRoot (m : ℕ) : kummerRing f r :=
  kummerRingι f r m (AdjoinRoot.root _)

lemma kummerRoot_pow (m : ℕ) : kummerRoot f r m ^ (r ^ m) = algebraMap A _ f := by
  rw [kummerRoot, ← map_pow, kummerStage_root_pow, kummerRingι_algebraMap]

lemma exists_kummerRingι_eq (x : kummerRing f r) : ∃ n y, kummerRingι f r n y = x := by
  obtain ⟨⟨n⟩, y, hy⟩ := Concrete.colimit_exists_rep (kummerDiagram f r) x
  exact ⟨n, y, hy⟩

/-- A stage of the Kummer tower of a unit `f` with `r` invertible is étale. -/
lemma etale_kummerStage (hf : IsUnit f) (hr : IsUnit (r : A)) (n : ℕ) :
    Algebra.Etale A (KummerStage f r n) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (KummerStage f r n) := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap A (KummerStage f r n)),
        ← map_one (algebraMap A (KummerStage f r n)), Subsingleton.elim (0 : A) 1]
    exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A _)
      ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩)
  · have hr₀ : r ≠ 0 := by
      rintro rfl
      simp at hr
    exact AdjoinRoot.etale_X_pow_sub_C (pow_ne_zero n hr₀) (by simpa using hr.pow n)
      hf

/-- The ring `A[f^{1/r^∞}]` is ind-étale over `A` if `f` is a unit and `r` is invertible. -/
theorem indEtale_kummerRing (hf : IsUnit f) (hr : IsUnit (r : A)) :
    Algebra.IndEtale A (kummerRing f r) := by
  rw [← RingHom.IndEtale.algebraMap_iff]
  refine (RingHom.IndEtale.iff_exists (CommRingCat.ofHom (algebraMap A (kummerRing f r)))).2
    ⟨ULift.{u} ℕ, inferInstance, inferInstance, kummerDiagram f r,
      { app n := CommRingCat.ofHom (algebraMap A _)
        naturality n m h := by
          ext a
          exact ((kummerStageMap f r (ULift.down_le.mpr (leOfHom h))).commutes a).symm },
      (colimit.cocone (kummerDiagram f r)).ι, colimit.isColimit _, fun n ↦ ⟨?_, ?_⟩⟩
  · exact RingHom.etale_algebraMap.mpr (etale_kummerStage f r hf hr n.down)
  · ext a
    exact kummerRingι_algebraMap f r n.down a

/-- The ring `A[f^{1/r^∞}]` is integral over `A`, for `r ≠ 0`. -/
theorem isIntegral_kummerRing (hr : r ≠ 0) : Algebra.IsIntegral A (kummerRing f r) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨n, y, rfl⟩ := exists_kummerRingι_eq f r x
  have : Module.Finite A (KummerStage f r n) :=
    (monic_X_pow_sub_C f (pow_ne_zero n hr)).finite_adjoinRoot
  exact IsIntegral.map_of_comp_eq (RingHom.id A) (kummerRingι f r n)
    (kummerRingι_comp_algebraMap f r n).symm (Algebra.IsIntegral.isIntegral y)

/-- The map `A → A[f^{1/r^∞}]` is injective, for `r ≠ 0`: an element of `A` vanishing in the
colimit vanishes in some stage `A[T]/(T^{rⁿ} - f)`, which is faithfully flat over `A`. -/
theorem injective_algebraMap_kummerRing (hr : r ≠ 0) :
    Function.Injective (algebraMap A (kummerRing f r)) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Function.injective_of_subsingleton _
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← kummerRingι_algebraMap f r 0, ← map_zero (kummerRingι f r 0)] at ha
  obtain ⟨⟨k⟩, h₁, h₂, hk⟩ := Concrete.colimit_exists_of_rep_eq (kummerDiagram f r)
    (i := ⟨0⟩) (j := ⟨0⟩) (algebraMap A (KummerStage f r 0) a) 0 ha
  have : Module.FaithfullyFlat A (KummerStage f r k) :=
    AdjoinRoot.faithfullyFlat_of_monic (monic_X_pow_sub_C f (pow_ne_zero k hr)) (by
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero (pow_ne_zero k hr))]
      exact_mod_cast pow_ne_zero k hr)
  refine FaithfulSMul.algebraMap_injective A (KummerStage f r k) ?_
  rw [map_zero, ← (kummerStageMap f r (ULift.down_le.mpr (leOfHom h₁))).commutes]
  rw [map_zero] at hk
  exact hk

/-- The map `Spec A[f^{1/r^∞}] → Spec A` is surjective, for `r ≠ 0`: `A → A[f^{1/r^∞}]` is
injective and integral. -/
theorem surjective_comap_algebraMap_kummerRing (hr : r ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kummerRing f r))) := by
  have := isIntegral_kummerRing f r hr
  have : FaithfulSMul A (kummerRing f r) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_algebraMap_kummerRing f r hr)
  exact Algebra.IsIntegral.comap_surjective _ _


/-- The map `Spec A[f^{1/r^∞}] ⟶ Spec A` is surjective if `r` is invertible in `A`. -/
lemma surjective_SpecMap_kummerRing {A : CommRingCat.{u}} (f : A) (r : ℕ) (hr : IsUnit (r : A)) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A (kummerRing f r)))) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨fun x ↦ (x.isPrime.ne_top (Subsingleton.elim _ _)).elim⟩
  have hr₀ : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨surjective_comap_algebraMap_kummerRing f r hr₀⟩

end Ring

end ProEtale

namespace Scheme.ProEt

section KummerCover

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (r : ℕ)

/-- The morphism `Spec Γ(X, U)[f^{1/r^∞}] ⟶ Spec Γ(X, U) ≅ U ⟶ X`. -/
noncomputable def kummerCoverHom : Spec (ProEtale.kummerRing f r) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (ProEtale.kummerRing f r))) ≫ hU.fromSpec

lemma weaklyEtale_kummerCoverHom (hf : IsUnit f) (hr : IsUnit (r : Γ(X, U))) :
    WeaklyEtale (kummerCoverHom hU f r) := by
  have := ProEtale.indEtale_kummerRing f r hf hr
  rw [kummerCoverHom]
  infer_instance

/-- The Kummer cover `Spec Γ(X, U)[f^{1/r^∞}] ⟶ X` of an affine open `U` of `X`, for a unit
`f ∈ Γ(X, U)` and `r` invertible on `U`, as an object of the small pro-étale site of `X`. -/
noncomputable def kummerCover (hf : IsUnit f) (hr : IsUnit (r : Γ(X, U))) : X.ProEt :=
  haveI := weaklyEtale_kummerCoverHom hU f r hf hr
  Scheme.ProEt.mk (kummerCoverHom hU f r)

variable (hf : IsUnit f) (hr : IsUnit (r : Γ(X, U)))

lemma kummerCover_left : (kummerCover hU f r hf hr).left = Spec (ProEtale.kummerRing f r) :=
  rfl

lemma kummerCover_hom : (kummerCover hU f r hf hr).hom = kummerCoverHom hU f r :=
  rfl

/-- The image of the Kummer cover `Spec Γ(X, U)[f^{1/r^∞}] ⟶ X` is `U`. -/
lemma range_kummerCoverHom (hr : IsUnit (r : Γ(X, U))) :
    Set.range (kummerCoverHom hU f r) = U := by
  have := ProEtale.surjective_SpecMap_kummerRing f r hr
  ext x
  rw [kummerCoverHom, ← hU.range_fromSpec]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨_, hy⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U) (ProEtale.kummerRing f r)))).surjective y
  exact ⟨z, hy⟩

end KummerCover

section Cover

variable {X : Scheme.{u}} {ι : Type*} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i))
  (f : ∀ i, Γ(X, U i)) (r : ℕ)

/-- Kummer covers over an affine open cover `U` of `X` form a pro-étale covering family: they
are the composites of the Zariski cover `U i ⟶ X` with the surjective, quasi-compact, weakly
étale morphisms `Spec Γ(X, U i)[f^{1/r^∞}] ⟶ U i`. -/
lemma ofArrows_kummerCoverHom_mem_proetalePrecoverage (hf : ∀ i, IsUnit (f i))
    (hr : ∀ i, IsUnit (r : Γ(X, U i))) (hcov : ⨆ i, U i = ⊤) :
    Presieve.ofArrows _ (fun i ↦ kummerCoverHom (hU i) (f i) r) ∈
      Scheme.proetalePrecoverage X := by
  have h₁ : Presieve.ofArrows _ (fun i ↦ (U i).ι) ∈ Scheme.proetalePrecoverage X := by
    refine Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩)
    have hx : x ∈ ⨆ i, U i := by
      rw [hcov]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, by rwa [Scheme.Opens.range_ι]⟩
  have h₂ (i : ι) : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Spec (ProEtale.kummerRing (f i) r))
      (fun _ ↦ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U i)
        (ProEtale.kummerRing (f i) r))) ≫ (hU i).isoSpec.inv) ∈
        Scheme.proetalePrecoverage (U i) := by
    have : IsAffine (U i) := hU i
    have := ProEtale.surjective_SpecMap_kummerRing (f i) r (hr i)
    have := ProEtale.indEtale_kummerRing (f i) r (hf i) (hr i)
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage inferInstance
  have h₃ := Precoverage.comp_mem_coverings _ h₁ _ h₂
  convert h₃ using 1
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨i⟩
    convert Presieve.ofArrows.mk (Y := fun p : Σ _ : ι, PUnit.{1} ↦
      Spec (ProEtale.kummerRing (f p.1) r)) ⟨i, PUnit.unit⟩ using 1
    rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    rfl
  · rintro _ _ ⟨⟨i, -⟩⟩
    convert Presieve.ofArrows.mk (Y := fun i ↦ Spec (ProEtale.kummerRing (f i) r)) i using 1
    rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    rfl

/-- Kummer covers over an affine open cover `U` of `X` cover the terminal object of `X_proét`. -/
theorem ofArrows_kummerCover_mem_topology (hf : ∀ i, IsUnit (f i))
    (hr : ∀ i, IsUnit (r : Γ(X, U i))) (hcov : ⨆ i, U i = ⊤) :
    Sieve.ofArrows (fun i ↦ kummerCover (hU i) (f i) r (hf i) (hr i))
      (fun _ ↦ (isTerminalMkId X).from _) ∈ topology X (Scheme.ProEt.mk (𝟙 X)) := by
  rw [mem_topology_iff]
  refine ⟨Presieve.ofArrows _ (fun i ↦ (isTerminalMkId X).from
    (kummerCover (hU i) (f i) r (hf i) (hr i))), ?_, Sieve.le_generate _⟩
  rw [mem_precoverage_iff, Presieve.map_ofArrows]
  exact ofArrows_kummerCoverHom_mem_proetalePrecoverage hU f r hf hr hcov

end Cover
section FixedRoots

variable {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
  {f : Γ(X, U)} (hf : IsUnit f) {r : ℕ} (hr : IsUnit (r : Γ(X, U)))

/-- A morphism `g` from the geometric generic point `Spec Kˢᵉᵖ` to a Kummer cover is the spectrum
of a ring map `ψ : Γ(X, U)[f^{1/r^∞}] → Kˢᵉᵖ` extending `Γ(X, U) → K → Kˢᵉᵖ`. -/
lemma exists_eq_SpecMap_of_genericPointSep_hom_kummerCover
    (g : genericPointSep X ⟶ kummerCover hU f r hf hr) :
    ∃ ψ : ProEtale.kummerRing f r ⟶ CommRingCat.of (SeparableClosure X.functionField),
      g.left = Spec.map ψ ∧ ∀ a : Γ(X, U), ψ (algebraMap Γ(X, U) _ a) =
        algebraMap X.functionField (SeparableClosure X.functionField)
          (X.germToFunctionField U a) := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  let g' : Spec (.of (SeparableClosure X.functionField)) ⟶ Spec (ProEtale.kummerRing f r) :=
    g.left
  refine ⟨Spec.preimage g', (Spec.map_preimage g').symm, fun a ↦ ?_⟩
  have hw := MorphismProperty.Over.w g
  rw [kummerCover_hom, kummerCoverHom, genericPointSep_hom, genericPointSepHom,
    ← hU.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk] at hw
  have hw' : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (ProEtale.kummerRing f r)) ≫
      Spec.preimage g') = Spec.map (X.presheaf.germ U (genericPoint X) hη ≫
        CommRingCat.ofHom (algebraMap X.functionField (SeparableClosure X.functionField))) := by
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, ← cancel_mono hU.fromSpec,
      Category.assoc, Category.assoc]
    exact hw
  exact ConcreteCategory.congr_hom (Spec.map_injective hw') a

/-- **Fixed roots.** Let `X` be integral with function field `K` containing primitive `rᵐ`-th roots
of unity for all `m`, let `g` be a morphism from the geometric generic point `Spec Kˢᵉᵖ` to the
Kummer cover of a unit `f` on a nonempty affine open `U`, and let `σ ∈ Gal(Kˢᵉᵖ/K)` fix `g`. Then
`σ` fixes every `rᵐ`-th root of `f` in `Kˢᵉᵖ`: one of them is the image of the root `f^{1/rᵐ}` of
the Kummer ring, which is fixed by `σ`, and any other one differs from it by an `rᵐ`-th root of
unity, which lies in `K`. -/
theorem genericPointSepAut_apply_eq_of_hom_kummerCover
    (hζ : ∀ m : ℕ, ∃ ζ : X.functionField, IsPrimitiveRoot ζ (r ^ m))
    (g : genericPointSep X ⟶ kummerCover hU f r hf hr)
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField] SeparableClosure X.functionField)
    (hσ : genericPointSepAut X σ ≫ g = g) (m : ℕ) (β : SeparableClosure X.functionField)
    (hβ : β ^ (r ^ m) = algebraMap X.functionField (SeparableClosure X.functionField)
      (X.germToFunctionField U f)) :
    σ β = β := by
  obtain ⟨ψ, hψ, hψa⟩ := exists_eq_SpecMap_of_genericPointSep_hom_kummerCover hU hf hr g
  have hψσ (x : ProEtale.kummerRing f r) : σ (ψ x) = ψ x := by
    have h : (genericPointSepAut X σ ≫ g).left = g.left := by rw [hσ]
    rw [MorphismProperty.Comma.comp_left, genericPointSepAut_left, hψ, ← Spec.map_comp] at h
    exact ConcreteCategory.congr_hom (Spec.map_injective h) x
  have hr₀ : r ≠ 0 := by
    rintro rfl
    have := hr.map (X.germToFunctionField U).hom
    simp at this
  have hc : algebraMap X.functionField (SeparableClosure X.functionField)
      (X.germToFunctionField U f) ≠ 0 :=
    ((hf.map (X.germToFunctionField U).hom).map (algebraMap _ _)).ne_zero
  set β₀ := ψ (ProEtale.kummerRoot f r m)
  have hβ₀ : β₀ ^ (r ^ m) = algebraMap X.functionField (SeparableClosure X.functionField)
      (X.germToFunctionField U f) := by
    rw [← map_pow, ProEtale.kummerRoot_pow, hψa]
  have hβ₀ne : β₀ ≠ 0 := by
    rintro h
    rw [h, zero_pow (pow_ne_zero m hr₀)] at hβ₀
    exact hc hβ₀.symm
  have hpow : (β / β₀) ^ (r ^ m) = 1 := by
    rw [div_pow, hβ, hβ₀, div_self hc]
  obtain ⟨ω, hω⟩ := hζ m
  have : NeZero (r ^ m) := ⟨pow_ne_zero m hr₀⟩
  obtain ⟨i, -, hi⟩ := (hω.map_of_injective
    (algebraMap X.functionField (SeparableClosure X.functionField)).injective).eq_pow_of_pow_eq_one
      hpow
  have hσζ : σ (β / β₀) = β / β₀ := by
    rw [← hi, map_pow, AlgEquiv.commutes]
  rw [← div_mul_cancel₀ β hβ₀ne, map_mul, hσζ, hψσ]

/-- **Fixed roots**, for a morphism `g` from the geometric generic point to an object `W` over a
Kummer cover: if `σ ∈ Gal(Kˢᵉᵖ/K)` fixes `g`, then `σ` fixes every `rᵐ`-th root of `f` in
`Kˢᵉᵖ`. -/
theorem genericPointSepAut_apply_eq_of_comp_kummerCover
    (hζ : ∀ m : ℕ, ∃ ζ : X.functionField, IsPrimitiveRoot ζ (r ^ m)) {W : X.ProEt}
    (g : genericPointSep X ⟶ W) (h : W ⟶ kummerCover hU f r hf hr)
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField] SeparableClosure X.functionField)
    (hσ : genericPointSepAut X σ ≫ g = g) (m : ℕ) (β : SeparableClosure X.functionField)
    (hβ : β ^ (r ^ m) = algebraMap X.functionField (SeparableClosure X.functionField)
      (X.germToFunctionField U f)) :
    σ β = β :=
  genericPointSepAut_apply_eq_of_hom_kummerCover hU hf hr hζ (g ≫ h) σ
    (by rw [← Category.assoc, hσ]) m β hβ

end FixedRoots

end Scheme.ProEt

end AlgebraicGeometry
